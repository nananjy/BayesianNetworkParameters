package 包名;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.List;

import AdjacencyTablesRepGraphs.*;
import BayesianNetwork.ConstructBN_adjacencylist;
import MarkovNetwork.ConstructMN_adjacencylist;
import ObservedSet.ObservedSet;
import Utils.FilePathUtils;
import Utils.VertexUtils;

/**
 * 生成贝叶斯网参数，通过邻接表表示图
 * 注：每个频繁集是有序的
 * 生成的参数项个数有2^47个，超出java数组的最大存放个数，出现内存溢出错误，
 * 因此，可以根据最大频繁集的个数，从2^47项中选择小于等于最大频繁集个数的有用项
 * @author 作者名
 */
public class LearningBNParameters {

	private List<VertexEntity> bayesianN;//存放有向图
	private String candiFreFilePath, freFilePath;//候选频繁集以及频繁集文件存放路径
	private ArrayList<String> parameterItemSet;//存放参数项集
	private List<Integer> adjaLoc;//存放选中发生的邻接点在参数项中的位置
	
	/**
	 * 输入为有向图、候选频繁文件名、频繁文件名的构造函数
	 * @param bayesianN 待赋值的有向图
	 * @param candiFreFileName 待赋值的候选频繁文件名
	 * @param freFileName 待赋值的频繁文件名
	 */
	public LearningBNParameters(List<VertexEntity> bayesianN, String candiFreFileName, String freFileName) {
		this.bayesianN = new ArrayList<VertexEntity>();//初始化有向图列表
		this.bayesianN.addAll(bayesianN);//赋值有向图
		this.candiFreFilePath = FilePathUtils.generateFilePath(candiFreFileName);//赋值候选频繁集文件路径
		this.freFilePath = FilePathUtils.generateFilePath(freFileName);//赋值频繁集文件路径
	}
	
	/**
	 * 计算BN参数表
	 * @param parameterTableFileName 待输出的参数表文件名
	 * @param maxFreFileName 待输入的频繁集文件名
	 */
	public void BNParameter(String parameterTableFileName, String maxFreFileName) {
		//获取方法开始运行的时间
		Date time = new Date();
		SimpleDateFormat sdf = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss aa");
		System.out.println("系统开始运行的时间为" + sdf.format(time));
		String parameterTableFilePath=FilePathUtils.generateFilePath(parameterTableFileName);//获取参数表文件路径
		int maxFrequencyLevel = VertexUtils.getMaxFreNum(maxFreFileName);//获取最大频繁集的项数
		try {
			//计算出的参数表写入文件parameterTableFile
			BufferedWriter bw = new BufferedWriter(new FileWriter(parameterTableFilePath));
			//1 得到以每个节点为汇聚点的邻接点集，即得到P(X|ABC)中的ABC
			for (int i = 0; i < this.bayesianN.size(); i++) {
				long startTime = System.currentTimeMillis();//获取系统当前的时间
				int adjVertexNum = 0;//记录节点i的邻节点个数,即节点的入度
				ArrayList<String> adjacentPointSet = new ArrayList<String>();//保存邻接点集
				EdgeEntity edgeEntity = this.bayesianN.get(i).getHeadEdgeLink();//获得与汇聚点直接相邻的边
				while (edgeEntity != null) {
					adjVertexNum++;
					adjacentPointSet.add(edgeEntity.getTailVertexLabel());
					edgeEntity = edgeEntity.getHeadEdgeNext();
				}
				//将汇聚节点的邻接点个数写入度中
				this.bayesianN.get(i).setInDegree(adjVertexNum);
				//2 得到每个节点的参数项
				this.parameterItemSet = new ArrayList<String>();//保存第i个节点的参数项集
				long parameterItemNum = (long)Math.pow(2, adjVertexNum);//保存第i个节点的参数项个数，参数项个数为2的adjVertexNum次方，大于等于1
				System.out.println("第" + i + "个节点的邻接点的个数为" + adjVertexNum + "，参数项个数为" + parameterItemNum);
				float[] parameterValueSet;//保存节点i的每个参数项对应的值,float数组只存放选中发生的邻接点个数小于最大频繁个数的项，经计算个数小于2^29（数组可存放的最大个数）
				//如果等于1，说明节点i没有邻接点，参数表存放节点i发生的概率
				if (parameterItemNum > 1) {
					//参数项集parameterItemSet存放组合C(M, N) + C(M, N-1) + ... + C(M, 1), M表示节点i的邻接点个数，N表示最大频繁集的项数
					String combine = "";//保存M个0的字符串，M为节点i的邻接点个数
					for (int j = 0; j < adjVertexNum; j++) {
						combine += "0";
					}
					this.adjaLoc = new ArrayList<Integer>();//存放选中发生的邻接点在参数项中的位置
					if (adjVertexNum > maxFrequencyLevel) {
						for (int level = maxFrequencyLevel; level > 0; level--) {
							ParameterItemSetByCombine(0, level, combine);
						}
					}else {
						for (int level = adjVertexNum; level > 0; level--) {
							ParameterItemSetByCombine(0, level, combine);
						}
					}
					parameterItemSet.add(combine);//将全0存入参数项集中
					System.out.println("第" + i + "个节点实际存入的参数项个数为" + parameterItemSet.size());
					/*
					 * 3 得到每个节点参数项对应的值
					 * 注意：参数项集parameterItemSet的大小不一定等于parameterItemNum
					 */
					parameterValueSet = new float[parameterItemSet.size()];//节点i的参数项对应的值集初始化
					for (int j = 0; j < parameterValueSet.length; j++) {
						parameterValueSet[j] = -1;
					}
					for (int j = 0;j < parameterItemSet.size(); j++) {
						if (parameterValueSet[j] != -1) {//超集已经对其子集赋值，直接跳过
							continue;
						}
						//3.1 找到每个参数项中选中发生的邻接点
						ArrayList<String> choosedAdjaPoint = new ArrayList<String>();//保存参数项中选中发生的邻接点
						for (int k = 0; k < adjVertexNum; k++) {
							if (parameterItemSet.get(j).charAt(k) == '1') {
								choosedAdjaPoint.add(adjacentPointSet.get(k));
							}
						}
						//3.2 比较选中发生邻接点个数与最大频繁项个数，若选中发生邻接点个数多，没有参数，置-2
						if (choosedAdjaPoint.size() > maxFrequencyLevel) {
							parameterValueSet[j] = -2;//-2表示~，不考虑条件概率
						} else {
							//3.2 若选中发生的邻接点个数少，将选中的项与频繁集对比
							//3.2.1 将频繁集转为数组表示0,1,2...
							BufferedReader frequency = new BufferedReader(new FileReader(this.freFilePath));//打开频繁集文件
							String itemSetLine = frequency.readLine();
							while (itemSetLine != null) {
								String[] itemSetStr = itemSetLine.split("\t");
								if((itemSetStr[0].equals("*")) && (Integer.parseInt(itemSetStr[1]) == choosedAdjaPoint.size())) {
									itemSetLine = frequency.readLine();
									while (itemSetLine != null) {
										itemSetStr = itemSetLine.split("\t");
										if (itemSetStr[0].equals("*")) {
											break;//没有找到与邻接点集匹配的频繁集,跳出
										}
										String[] freStrSets = itemSetStr[0].split(",");
										int num = 0;//保存选中发生的邻接点与频繁集匹配的个数
										for (int k = 0; k < choosedAdjaPoint.size(); k++) {//前提条件，频繁集有序，选中发生的邻接点有序，不能保证
											for (int k2 = 0; k2 < freStrSets.length; k2++) {
												if (freStrSets[k2].equals(choosedAdjaPoint.get(k))) {
													num++;
													break;
												}
											}
											if (num != k+1) {//num==k+1说明找到匹配的邻接点
												break;//当前频繁集freStrSets不包含选中发生的邻接点
											}
										}
										//若选中发生的邻接点集是频繁集，计算此邻接点集即参数项的值
										if (choosedAdjaPoint.size() == num) {
											System.out.println(choosedAdjaPoint.toString() + "是频繁集");
											//计算邻接点集分母ABC的概率值，并将频繁集的子集对应的邻接点集置-2，(删除此频繁集及其子集)
											int[] location = ChoosedAdjaSubPoint(j, adjVertexNum);//存放子集参数项的位置
											for (int k = 0; k < location.length; k++) {//置-2
												if (parameterValueSet[location[k]] == -1) {
													parameterValueSet[location[k]] = -2;
												}
											}
											//5.判断概率分子是否属于一个频繁集，若是，计算分子及概率值；若不是，选择概率最小值P(X|C).
											if (choosedAdjaPoint.size()+1 <= maxFrequencyLevel) {
												float fenmu = Float.parseFloat(itemSetStr[2]);//分母概率值
												itemSetLine = frequency.readLine();
												while (itemSetLine != null) {
													itemSetStr = itemSetLine.split("\t");
													if((itemSetStr[0].equals("*")) && (Integer.parseInt(itemSetStr[1]) == choosedAdjaPoint.size()+1)) {
														itemSetLine = frequency.readLine();
														while (itemSetLine != null) {
															itemSetStr = itemSetLine.split("\t");
															if (itemSetStr[0].equals("*")) {
																break;//没有找到与分子集合相匹配的频繁集
															}
															ArrayList<String> choosedPoint = new ArrayList<String>();//存入分子,无序
															choosedPoint.add(bayesianN.get(i).getLabel());
															choosedPoint.addAll(choosedAdjaPoint);
															String[] freStrSets2 = itemSetStr[0].split(",");//保存频繁集
															int num2 = 0;//临时变量，记录分子与频繁集匹配的个数
															for (int k = 0; k < choosedPoint.size(); k++) {
																for (int k2 = 0; k2 < freStrSets2.length; k2++) {
																	if (freStrSets2[k2].equals(choosedPoint.get(k))) {
																		num2++;
																		break;
																	}
																}
																if (num2 != k+1) {//num==k+1说明找到匹配的分子节点
																	break;
																}
															}
															if (choosedPoint.size() == num2 && fenmu != 0) {
																//分子属于一个频繁集，计算概率P(X|ABC).
																float fenzi = Float.parseFloat(itemSetStr[2]);
																parameterValueSet[j] = fenzi/fenmu;
																break;
															}
															itemSetLine = frequency.readLine();
														}
														break;
													}
													itemSetLine = frequency.readLine();
												}
											}
											//分子不属于一个频繁集，选择概率最小值P(X|C)
											if (parameterValueSet[j] == -1) {
												float temperateParameter = 2;//临时变量，存放参数
												for (int k = 0; k < choosedAdjaPoint.size(); k++) {
													ArrayList<String> fenZiSet = new ArrayList<String>();//存放分子集合的数组
													float fenmu = 0, fenzi = 0;
													if (choosedAdjaPoint.get(k).compareTo(bayesianN.get(i).getLabel()) > 0) {
														fenZiSet.add(bayesianN.get(i).getLabel());
														fenZiSet.add(choosedAdjaPoint.get(k));
													}else {
														fenZiSet.add(choosedAdjaPoint.get(k));
														fenZiSet.add(bayesianN.get(i).getLabel());
													}
													//分子集合可能不是频繁集，因此读取候选频繁集文件
													BufferedReader candiFrequency = new BufferedReader(new FileReader(candiFreFilePath));
													String candiItemSetLine = candiFrequency.readLine();
													while (candiItemSetLine != null) {
														String[] candiItemSet = candiItemSetLine.split("\t");
														if (candiItemSet[0].equals("*")) {
															if (candiItemSet[1].equals("1")) {
																candiItemSetLine = candiFrequency.readLine();
																while (candiItemSetLine != null) {
																	candiItemSet = candiItemSetLine.split("\t");
																	if (candiItemSet[0].equals("*")) {
																		System.out.println("候选频繁文件中没有找到分母,程序运行退出");
																		System.exit(0);
																	}
																	if (candiItemSet[0].equals(choosedAdjaPoint.get(k))) {
																		fenmu = Float.parseFloat(candiItemSet[2]);
																		break;//找到分母对应的频率
																	}
																	candiItemSetLine = candiFrequency.readLine();
																}
															}else if(candiItemSet[1].equals("2")) {
																candiItemSetLine = candiFrequency.readLine();
																while (candiItemSetLine != null) {
																	candiItemSet = candiItemSetLine.split("\t");
																	if (candiItemSet[0].equals("*")) {
																		System.out.println("候选频繁文件中没有找到分子,程序运行退出");
																		System.exit(0);
																	}
																	String[] candiFreItem = candiItemSet[0].split(",");
																	if (candiFreItem[0].equals(fenZiSet.get(0)) && candiFreItem[1].equals(fenZiSet.get(1))) {
																		fenzi = Float.parseFloat(candiItemSet[2]);
																		if (fenmu != 0 && (fenzi/fenmu < temperateParameter)) {
																			temperateParameter = fenzi/fenmu;
																		}
																		break;
																	}
																	candiItemSetLine = candiFrequency.readLine();
																}
																break;
															}
														}
														candiItemSetLine = candiFrequency.readLine();
													}
													candiFrequency.close();
												}
												if (temperateParameter == 2) {
													System.out.println("候选频繁集中没有分子和分母的概率值,程序运行退出");
													System.exit(0);
												}else {
													parameterValueSet[j] = temperateParameter;
												}
											}
											break;
										}
										itemSetLine = frequency.readLine();
									}
									if (parameterValueSet[j] == -1) {
										//若选中发生的邻接点不是频繁集（分母不是频繁集），将邻接点集置-2；
										parameterValueSet[j] = -2;
									}
									break;
								}
								itemSetLine = frequency.readLine();
							}
							frequency.close();
						}
					}
				}else {
					parameterValueSet = new float[0];
				}
				System.out.println("准备将结果转为字符串写入文件");
				String tempStr = "*\t" + i + "\t";
				if (adjacentPointSet.size() == 0) {
					bw.write(tempStr);
					bw.newLine();
					bw.flush();
				}else {
					tempStr += adjacentPointSet;
					bw.write(tempStr);
					System.out.println("成功写入adjacentPointSet");
					bw.newLine();
					bw.flush();
					for (int k = 0; k < parameterItemSet.size()-1; k++) {
						bw.write(parameterItemSet.get(k) + "\t");
						if (k % 100000 == 0) {
							System.out.println("字符串保存参数项的个数为" + k);
						}
					}
					bw.write(parameterItemSet.get(this.parameterItemSet.size()-1));
					System.out.println("成功写入parameterItemSet");
					bw.newLine();
					bw.flush();
					for (int k = 0; k < parameterValueSet.length-1; k++) {
						bw.write(parameterValueSet[k] + "\t");
						if (k % 100000 == 0) {
							System.out.println("字符串保存参数项值的个数为" + k);
						}
					}
					bw.write(parameterValueSet[parameterValueSet.length-1] + "");
					System.out.println("成功写入parameterValueSet");
					bw.newLine();
					bw.flush();
				}
				System.gc();//提醒回收，不一定立即回收
				System.out.println("第" + i + "个节点" + bayesianN.get(i).getLabel() + "的参数表写入完成,用时" + (System.currentTimeMillis() - startTime) + "s");
			}
			bw.close();
			System.out.println("OK");
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	/**
	 * 获取参数项集
	 * 组合实现C(M, N) + C(M, N-1) + ... + C(M, 1), M表示节点i的邻接点个数，N表示最大频繁集的项数
	 * @param index 参数项字符串下标
	 * @param k 待组合的邻接点个数，范围1~N
	 * @param combine 邻接点M个0的字符串
	 */
	private void ParameterItemSetByCombine(int index, int k, String combine) {
		if(k == 1){
			for (int i = index; i < combine.length(); i++) {
				this.adjaLoc.add(i);//第i个选中发生的邻接点,存放到选中发生邻接点列表adjaLoc
				String parameter = combine;//保存参数项
				for (Integer tmp : this.adjaLoc) {
					parameter = parameter.substring(0, tmp) + "1" + parameter.substring(tmp +1);
				}
				//将生成的参数项存入参数项集列表parameterItemSet
				parameterItemSet.add(parameter);
				this.adjaLoc.remove((Object)i);//选中发生的邻接点i,从选中发生邻接点列表adjaLoc中移除
			}
		}else if(k > 1){
			for (int i = index; i <= combine.length() - k; i++) {
				//将第i个邻接点存放到选中发生的邻接点列表adjaLoc
				this.adjaLoc.add(i);
				//递归，直到得到k个邻接点的邻接点列表
				ParameterItemSetByCombine(i + 1, k - 1, combine);
				//包含第i个邻接点的参数项已经输出完成，将其从List数组adjaLoc中删除
				this.adjaLoc.remove((Object)i);
			}
		}
	}
	
	/**
	 * 找出频繁集对应的子集，不包括自身,返回子集在参数表中的位置
	 * @param j 参数项集中的第j个参数项
	 * @param nodeNum 邻接点个数
	 * @return 参数项的子集在参数表中的位置
	 */
	private int[] ChoosedAdjaSubPoint(int j, int nodeNum) {
		int choosedFreSetNum = 0;//选中的邻接点个数
		int[] kLocation = new int[nodeNum];//存放选中发生的邻接点在参数项（邻接点集）中的位置
		for (int i = 0; i < kLocation.length; i++) {//初始化选中发生的邻接点位置
			kLocation[i] = -1;
		}
		for (int k = 0; k < nodeNum; k++) {
			if (parameterItemSet.get(j).charAt(k) == '1') {
				kLocation[choosedFreSetNum++] = k;//将选中发生的邻接点在邻接点集中的位置k赋值给kLocation
			}
		}
		int subSetNum = (int) Math.pow(2, choosedFreSetNum) - 1;//保存第j个参数项的子集个数，不包含自身
		int[] location = new int[subSetNum];//保存子集在参数项集中的位置
		int loc = 0;//存放子集在参数项集中的位置数组location的下标
		for (int i = subSetNum-1; i >= 0; i--) {//遍历所有的子集
			int index = choosedFreSetNum - 1;//存放选中发生的邻接点个数-1
            int subNum = i;//用来存放第i个子集
            ArrayList<Integer> subLoc = new ArrayList<Integer>();//存放子集中选中节点在邻接点集中的位置
            while(subNum > 0){
                if((subNum & 1) > 0){
                	subLoc.add(kLocation[index]);
                }
                subNum >>= 1;
                index--;
            }
            //获取子集对应的参数项Item
            String Item = "";//存放子集对应的参数项
            int l2 = subLoc.size() - 1;
            for (int l = 0; l < nodeNum; l++) {
            	if (l2 >= 0) {
					if (l == subLoc.get(l2)) {
						Item += "1";
						l2--;
						continue;
					}
				}
				Item += "0";
			}
            /*
             * 遍历parameterItemSet，找子集参数项的位置
             */
            for (int l = 0; l < this.parameterItemSet.size(); l++) {
				if (Item.equals(this.parameterItemSet.get(l))) {
					location[loc++] = l;//存放子集参数项的位置
					break;
				}
				if (l == parameterItemSet.size() -1) {
					System.out.println("没有找到对应子集" + Item + ",程序运行出错，退出");
					System.exit(0);
				}
			}
		}
		return location;
	}
	
	public static void main(String[] args) {
		//得到无向图
		ConstructMN_adjacencylist constructMN = new ConstructMN_adjacencylist("weibo\\constructmn_qu4netqu.txt");
		List<VertexEntity> markovN = constructMN.ConstructMarkovN();
		//得到观测节点
		ObservedSet observedSet = new ObservedSet("weibo\\frequency_qu4netqu.txt", 10);//第二个参数为选取的观测点个数
		List<String> observedVertexs = observedSet.ObservedItemsets();
		System.out.println("观测点集：" + observedVertexs);
		//得到有向图
		ConstructBN_adjacencylist constructBN = new ConstructBN_adjacencylist();
		List<VertexEntity> bayesianN = constructBN.ConstructBayesianN(markovN, observedVertexs);
		//得到参数表
		LearningBNParameters learningBNParameters = new LearningBNParameters(bayesianN, "candfrequency.txt", "frequency.txt");
		learningBNParameters.BNParameter("parameterTable.txt", "constructmn.txt");//constructmn.txt是倒排后的频繁集文件
	}
}
