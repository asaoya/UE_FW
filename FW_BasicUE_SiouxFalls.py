#这段代码中，并不用求UE的目标函数，只要目标z关于步长α的导数，线搜索使用了二分法，最短路使用Dijkstra
import os
import heapq
import math
import time


#第一步：基本类定义（路段，节点，OD对）
class node():#节点类，包含每个节点的坐标信息
    def __init__(self):
        self.node_id=None
        self.pos_x=None
        self.pos_y=None
        self.origin=-1
        self.innode=[]  #进入节点路段集合
        self.outnode=[]  #离开节点路段集合

class link(): #路段类，包含路段的起讫点、自由流行驶时间、容量、BRP路阻函数的参数
    def __init__(self):
        self.link_id=None
        self.init_node=None#起点
        self.term_node=None#终点
        self.length=None
        self.capacity=None
        self.free_flow_time=None
        self.traveltime=None 
        self.B=0.15    #SiouxFalls网络中路网B与Power系数值均相等，统一设置一个初始值
        self.Power=4

class OD():             #OD类，记录每一个OD需求信息，包含起点、重点、流量需求
    def __init__(self):
        self.OD_id=None
        self.origin_node=None       #这里放的是起始节点的id
        self.destinations=[]        
        self.ods_demand=[]

#第二步：定义路网核心函数（路网信息导入、UE分配计算等）
class network():#网络类，核心函数
    def __init__(self):
        self.Nodes = []       #网络包含节点集合，已按id顺序排列好
        self.Links = []        #路段集合，已按id顺序排列好
        self.Origins = []      #看似是起始点集合，实则存储的都是OD类，已按id顺序排列好
        self.num_Nodes = 0     #节点个数
        self.num_Links = 0     #路段个数
        self.num_Origins = 0   #起点个数
        self.Linkflows = []    #路段流量集合,按路段id顺序排列？？
        self.Linktimes = []#路段行驶时间集合
        self.max_iter = 1e5 + 1   #最大迭代次数
        self.max_err = 1e-4  #UE最大误差
        self.bisection_err = 0.01   #二分法的左右边界误差
        self.err = 1    #初始UE误差
        self.Djpathcost = [None] * 24   #最短路阻抗集合（Dijkstra算法求得）,第i个元素是节点i到所有节点的最短阻抗列表
        self.Djpath = [None] * 24       #最短路集合,第i个元素是节点i到所有节点的最短路径列表组成的列表

    def read_tntp_node_file(self,file_path):
        #nodes = {}
        with open(file_path, 'r') as f:
            lines = f.readlines()
            for line in lines[1:]:  # 跳过表头
                cleaned_line = line.strip().replace(';', '')     #去除分号
                node_id, x, y = map(float , cleaned_line.split())
                newnode = node()
                newnode.node_id=int(node_id)
                newnode.pos_x=int(x)
                newnode.pos_y=int(y) 
                self.Nodes.append(newnode)
                self.num_Nodes += 1
        f.close() 
        #return nodes
    
    def read_tntp_net_file(self,file_path):
        #links = []
        with open(file_path, 'r') as f:
            lines = f.readlines()
            # 寻找数据起始行
            data_start_index = 0
            for i, line in enumerate(lines):
                if line.startswith("~"):
                    data_start_index = i + 1
                    break
            id = 1
            # 从数据起始行开始解析，只保存前五列
            for line in lines[data_start_index:]:     
                init_node, term_node, capacity, length, free_flow_time = map(float, line.split(None, 5)[:5])
                newlink=link()
                newlink.link_id=id
                newlink.init_node=int(init_node)                
                newlink.term_node=int(term_node)
                newlink.free_flow_time=free_flow_time      
                newlink.capacity=capacity
                newlink.length=length 
                self.Nodes[int(init_node)-1].outnode.append(int(term_node))                 #储存每个节点的进入和流出的节点id
                #self.Nodes[newlink.init_node-1].outnode.append(int(term_node))
                self.Nodes[int(term_node)-1].innode.append(int(init_node))
                self.Links.append(newlink)
                id += 1
                self.num_Links += 1
        f.close() 
        #return links    

    def read_tntp_od_file(self, path):
        with open(path, 'r') as f:
            lines = f.readlines()

            current_origin = None  # 当前正在处理的OD对象
            for line in lines:
                if line.startswith("Origin"):
                    # 处理"Origin"行，创建新的OD对象
                    self.num_Origins += 1
                    if current_origin is not None:    #如果从origin 2 开始，需要保存上一个origin的数据，会漏掉origin 24
                        self.Origins.append(current_origin) 
                    parts = line.split()                    
                    current_origin = OD()
                    current_origin.OD_id = int(parts[1])    #取出origin后面的数字
                    current_origin.origin_node = current_origin.OD_id     
                    # self.Origins[current_origin.id] = current_origin
                elif current_origin is not None:
                    # 处理包含目的节点和需求的行
                    parts = line.split(';')
                    dest_and_demand = parts[:-1]  # 去除最后的空元素
                    for item in dest_and_demand:
                        dest, demand = map(float, item.split(':'))
                        current_origin.destinations.append(int(dest))
                        current_origin.ods_demand.append(demand)                                   
                    # self.Origins[current_origin.id].destinations.append(current_origin.destinations)
            # 在读取完成后，检查是否有未添加到 Origins 列表中的 current_origin，即把最后一个origin 24补充上了
            if current_origin is not None:
                self.Origins.append(current_origin)                   
        f.close
    
    def Dijkstra(self, start, destinations):  #输入：起始点id 和 目标点id的列表
        # 输出：到各终点如{4: {'distance': 4.0, 'path': [3, 4]}格式组合的字典
        # 初始化距离和路径字典
        shortest_distances = {node.node_id: float('inf') for node in self.Nodes}
        shortest_paths = {node.node_id: [] for node in self.Nodes}

        # 使用优先队列（最小堆）存储节点和距离信息
        priority_queue = [(0, start)]
        heapq.heapify(priority_queue)
        # 设置起点的距离为0
        shortest_distances[start] = 0

        while priority_queue:
            current_distance, current_node_id = heapq.heappop(priority_queue)
            # 如果当前距离大于已知的最短距离，则跳过
            if current_distance > shortest_distances[current_node_id]:
                continue
            current_node = self.Nodes[current_node_id - 1]

            # 遍历当前节点的邻居
            for neighbor_id in current_node.outnode:
                # neighbor = self.Nodes[neighbor_id - 1]
                link = next(link for link in self.Links if link.init_node == current_node_id and link.term_node == neighbor_id)
                new_distance = current_distance + link.traveltime
                # 如果新的距离比已知的最短距离小，则更新距离和路径
                if new_distance < shortest_distances[neighbor_id]:
                    shortest_distances[neighbor_id] = new_distance
                    shortest_paths[neighbor_id] = shortest_paths[current_node_id] + [current_node_id]
                    # 更新优先队列
                    heapq.heappush(priority_queue, (new_distance, neighbor_id))
        # 构建最终结果字典
        result = {}
        for destination in destinations:
            result[destination] = {
                'distance': shortest_distances[destination],
                'path': shortest_paths[destination] + [destination]
            }
        return result     
        
    def all_or_nothing(self):        # 应该返回一个AON分配后的路段流量列表
        # 初始化link flows为0 
        link_flows = [0]*len(self.Links)  # list(self.Linkflows)     
        for i,link in enumerate(self.Links):          # 使用BPR函数计算link travel time
            link.traveltime = link.free_flow_time * (1 + link.B * (self.Linkflows[i] / link.capacity) ** link.Power)               

        # 遍历每个OD对
        for i, origin in enumerate(self.Origins):  
            # print('we now at OD', i + 1)  
            Dj_result = self.Dijkstra(origin.origin_node, origin.destinations)   # 获取1 O-all D最短路径            
            self.Djpath[i] = []            #储存节点i+1到所有其他节点的最短路径
            self.Djpathcost[i] = []    
            
            # 保存1-to-all最短路径及最短距离   
            for destination, info in Dj_result.items():
                self.Djpathcost[i].append(info['distance']) 
                self.Djpath[i].append(info['path'])

            for j,dest in enumerate(origin.destinations):     #也可以不需要enumerate，j=dest-1            
                od_flow = origin.ods_demand[j]    # 计算OD对的流量        
                if i != j:  # 排除同一个节点的情况
                    shortest_path = self.Djpath[i][j]    # node i+1 to node j+1 的最短路径
                    # print(f'from node {i+1} to node {j+1}, shortest path is',shortest_path)
                    # 分配流量到构成最短路径的每一条路段上上
                    for k in range(len(shortest_path) - 1) :
                        init_node = shortest_path[k]
                        term_node = shortest_path[k + 1]
                        # 找到对应的link
                        link = next(link for link in self.Links if link.init_node == init_node and link.term_node == term_node)                        
                        # 更新link flow
                        link_flows[link.link_id - 1] += od_flow   
            # print(f'from node {i+1} to all other nodes shortest path',self.Djpath[i])
            # print(f'from node {i+1} to all other nodes shortest path cost',self.Djpathcost[i])
            # print(f'link flows of all links after assignment of OD {i+1} ',link_flows )
        # self.Linkflows = link_flows
        return link_flows
  
    def Optfunction(self,Descent,Lamuda):#为用二分法求UE目标在下行方向上的最优步长， 要求UE目标关于λ的导数
    #输入下降方向和步长,输出下降流量乘以每条路段上的出行时间的总和 (y-v)*t_a{v+λ(y-v)} 
        Sum = 0
        for i in range(len(self.Links)):
            x = self.Linkflows[i] + Lamuda*Descent[i]    # x=v+λ(y-v)
            Sum += Descent[i]*(self.Links[i].free_flow_time*(1+self.Links[i].B*(x/self.Links[i].capacity)**self.Links[i].Power))
        return Sum
    
    def Frank_Wolfe(self):                #Frank-Wolfe主函数
        
        iter = 0          #迭代次数
        self.Linkflows = [0 for i in range(len(self.Links))]   # 初始化为0流量        
        self.Linkflows = list(self.all_or_nothing())     # 做一次AON分配，用list函数复制列表，否则直接=会使两个变量名指向同一个列表

        while iter <= self.max_iter and self.err > self.max_err :      # 当误差未达到收敛标准时
            oldlinkflow = list(self.Linkflows)            
            auxi_linkflow = list(self.all_or_nothing())    
            print('-'*32, f'at iteration {iter}', '-'*32)
            # print('the old link flow is', oldlinkflow)
            # print('the auxiliary link flow is', auxi_linkflow)     
            Descent = []         #下降方向就是AON分配的辅助流减去上一次迭代结果的路段流
            for i in range(len(self.Links)):
                Descent.append(auxi_linkflow[i] - oldlinkflow[i])
            
            #二分法求最优步长，optfunction一定是增函数
            Lam = 0
            left = 0       
            right = 1
            mid = 0
            f_left = self.Optfunction(Descent,left)      
            f_right = self.Optfunction(Descent,right)      
            # print('if move a zero step length', self.Optfunction(Descent,left))
            # print('if move the whole step length', self.Optfunction(Descent,right))            
            f_mid = 0

            if f_left*f_right > 0:    # 检验无误
                if abs(f_left) > abs(f_right):
                    Lam = right
                    print('we take the right point')
                else:
                    Lam = left   
                    print('we take the left point')
            else:              
                while right - left > self.bisection_err:
                    mid = (left+right)/2
                    f_left = self.Optfunction(Descent,left)
                    f_right = self.Optfunction(Descent,right)
                    f_mid = self.Optfunction(Descent,mid)
                    if f_left*f_mid > 0:
                        left = mid
                    else: right = mid
                Lam=(left+right)/2

            # print(f'the current interval [{left},{right}],the derivate is [{f_left},{f_right}], the optimal step length is {Lam}')

            for i in range(len(self.Links)): #更新路段流量
                self.Linkflows[i] += Lam*Descent[i]             
            # print('the optimal step length in line search is', Lam)
            # print('if move a Lam step length', self.Optfunction(Descent,Lam))
            # print('after a movement, the new link flow is', self.Linkflows)
            iter += 1
            sum1 = 0 
            sum2 = 0
            for i in range(len(self.Links)): 
                sum1 += (self.Linkflows[i] - oldlinkflow[i]) ** 2 
                sum2 += (oldlinkflow[i])
            self.err =  math.sqrt(sum1) / sum2            
            print('the error is',self.err)
        return(self.Linkflows)

start_time = time.time()
net=network()  #定义一个network类
# 读取路网文件
current_directory = os.path.dirname(os.path.realpath(__file__))  # 获取当前文件所在目录
# 构建TNTP文件的完整路径
net_file_path = os.path.join(current_directory, 'SiouxFalls_net.tntp')
node_file_path = os.path.join(current_directory, 'SiouxFalls_node.tntp')
od_file_path = os.path.join(current_directory, 'SiouxFalls_trips.tntp')
# 读取文件
net.read_tntp_node_file(node_file_path)
net.read_tntp_net_file(net_file_path)
net.read_tntp_od_file(od_file_path)
nodes_data = net.Nodes
links_data = net.Links
ods_data = net.Origins

print('the total node numbers',net.num_Nodes)
print('the total link numbers',net.num_Links)
print('the total OD numbers(counted by origin)',net.num_Origins)


net.max_err = 1e-5
net.max_iter = 1e5 + 1
net.bisection_err = 1e-4
net.Frank_Wolfe()
print('the final link flows are', net.Linkflows)

end_time = time.time()
print(f'finish the whole program need {end_time - start_time} sec')


""" self.Linkflows = [4503.698371489499, 8127.281108842221, 4527.281108842221, 5966.0982318035685, 8103.698371489499, 14020.919663567121,
                           10032.30829921499, 14042.627330058698, 18020.919663567114, 5200.000000000116, 18042.627330058694, 8785.629077639678, 
                           15797.690446241484, 5989.680969156286, 8791.327461431007, 12489.327449129185, 12132.01850950465, 15846.374460437504, 
                           12518.60857027322, 12055.387894736832, 6887.888720337436, 8379.521402310349, 15813.699728941765, 6845.581847917995, 
                           21752.1085983235, 21825.811008604327, 17732.078778072755, 23136.5419535821, 11047.85346788383, 8099.999999999884, 
                           5300.000000000116, 17611.340937606896, 8364.96651833615, 9774.762887388137, 9987.017895370682, 8407.049710530553, 
                           12297.27481755115, 12394.067605901248, 11105.932394098752, 9811.94185472785, 9020.801634398467, 8391.009501822839, 
                           23203.866597186694, 9069.136175685759, 19071.86442727469, 18403.872616674165, 8374.478781106, 11074.969075025914, 
                           11670.851519401325, 15361.003571189518, 8100.000000000116, 11662.528666662036, 9944.76426894682, 15923.00507520534, 
                           15391.399409866552, 19028.985061684893, 19110.690570411567, 9936.44141620753, 8671.565066658124, 19036.011515129736, 
                           8702.068357055703, 6307.843063951851, 7000.000000000116, 6245.372807794292, 8596.480709599658, 10311.610293483, 
                           18380.705658429186, 7000.000000000116, 8603.767229531128, 9654.86645354351, 8379.853927875274, 9638.986015230008, 
                           7891.114888965868, 11102.72518244885, 10241.853517393949, 7864.07887670481] # 10w次迭代的结果        
        standard_flows = [4520.2,8097.58,4497.56,5992.61,8120.22,14041.5,9989.91,14017.9,18039.3,5308.79,18015.7,8803.59,15802.2,5969.97,8796.23,
                          12523.8,12046.6,15862.7,12493.8,12103.9,6837.27,8404.11,15786,6884.07,21817.7,21748.4,17604.1,23196,11070.5,8100.35,
                          5208.78,17729.4,8404.42,9816.35,10036.1,8367.08,12393.8,12302.6,11111.1,9778.96,9078.87,8390.82,23126.7,9036.26,19116,
                          18381.2,8384.58,11045.7,11675.6,15348.7,8099.81,11687.2,9941.22,15805.5,15292.7,19008.2,19081,9952.34,8705.95,18994.8,
                          8682.09,6244.49,7002.01,6306.38,8606.34,10256.4,18404.3,7002.93,8617.64,9624.05,8396.05,9659.39,7859.91,11119.9,10307,
                          7900.48]
        self.Linkflows = list(standard_flows) """