(*NAME: Konstantin Shvedov*)

(*Filter function*)
fun filter pred [] = []
	| filter pred (x::rest) = if pred x then x::(filter pred rest)
	else (filter pred rest);
	
(*Map Function*)
fun map f [] = []
	| map f (x::rest) = (f x)::(map f rest);
	
(*Fold Function*)
fun fold f base [] = base
| fold f base (x::rest) = f x (fold f base rest);

(*Print Depth Parameter*)
Control.Print.printDepth := 200;

(***********************************************************************************************************)
(*Question 1a*)
(*Takes and int and an int list and returns an int list*)
(*with the number of elements that add up to less than the input int*)
(***********************************************************************************************************)
fun numbersToSum sum [] = []
	| numbersToSum sum (x::rest) =
	if (sum - x) > 0 then x::(numbersToSum (sum-x) rest)
	else numbersToSum sum [];

(***********************************************************************************************************)
(*Question 1b*)
(*Tail recursive version of Question 1a*)
(***********************************************************************************************************)
fun numbersToSumTail sum [] = []
	| numbersToSumTail sum List =
	let
		fun addUp cur [] = cur
			| addUp cur (x::rest) = (addUp (cur+x) rest)
	in
		if addUp 0 List < sum then List
		else numbersToSumTail sum (rev (tl (rev List)))
	end;

(***********************************************************************************************************)
(*Question 2*)
(*This function Takes a predicit function and a list*)
(*Then return a tuple of two lists, first has values*)
(*that returned true from the predicate function and*)
(*the other one is with false*)
(***********************************************************************************************************)

fun partition F L =
		(filter F L, filter (not o F) L);

(***********************************************************************************************************)
(*Question 3*)
(*Checks if everything is unqique within the list, and returns true or false accordingly*)
(***********************************************************************************************************)
fun areAllUnique [] = true
	| areAllUnique nList =
	let
		fun countInList [] elem = 0
		| countInList (compareElem::listOfElem) elem =
			if elem = compareElem then (countInList listOfElem elem) + 1
			else (countInList listOfElem elem)
			
		fun uniqueFilterHelper bool =
			if bool = 1 then false
			else true
	in
		if filter uniqueFilterHelper (map (countInList nList) nList) = [] then true
		else false
	end;

(***********************************************************************************************************)
(*Question 4 A*)
(*This function excepts a list of lists and adds up all the values within*)
(***********************************************************************************************************)
fun sum nList =
	let
		fun addUp x y = x + y

		fun sumFoldHelper [] = 0
			|sumFoldHelper nList =
			fold addUp 0 nList

		fun mapHelper nList = map sumFoldHelper nList
	in
		sumFoldHelper (mapHelper nList)
	end

(***********************************************************************************************************)
(*Question 4 B*)
(*This function excepts a list of SOME lists and adds up all the values within and returns a SOME value*)
(***********************************************************************************************************)
fun sumOption nList =
	let
		fun addUpOp x y = SOME((getOpt(x, 0)) + (getOpt(y, 0)))
			
		fun sumOpFoldHelper [] = NONE
			|sumOpFoldHelper nList =
			if fold addUpOp NONE nList = SOME 0 then NONE
			else fold addUpOp NONE nList

		fun mapHelper nList = map sumOpFoldHelper nList
	in
		sumOpFoldHelper (mapHelper nList)
	end

(***********************************************************************************************************)
(*Question 4 C*)
(*This function excepts a list of lists and adds up all the values within*)
(*Only this function uses a premade datatype by the user either*)
(***********************************************************************************************************)

datatype either = IString of string | IInt of int;

fun sumEither nList =
	let
		fun str2int s = valOf(Int.fromString(s))
		
		fun addUp (IString (x)) (IString (y)) = IInt((str2int x)+(str2int y))
			| addUp (IString (x)) (IInt (y)) = IInt((str2int x) + y)
			| addUp (IInt (x)) (IString (y)) = IInt(x + (str2int y))
			| addUp	(IInt (x)) (IInt (y)) = IInt(x + y)
			
		fun sumFoldHelper [] = IInt(0)
			|sumFoldHelper nList =
			fold addUp (IInt(0)) nList

		fun mapHelper nList = map sumFoldHelper nList
	in
		sumFoldHelper (mapHelper nList)
	end

(***********************************************************************************************************)
(*Question 5 A*)
(*This function prints out the tree in post order*)
(***********************************************************************************************************)
datatype 'a Tree = LEAF of 'a | NODE of 'a * ('a Tree) * ('a Tree);

fun	depthScan (LEAF (n)) = [n]
	| depthScan (NODE (n, t1, t2)) = (depthScan (t1))@((depthScan(t2))@[n]);

(***********************************************************************************************************)
(*Question 5 B*)
(*This function searches a Tree in post order to find a value and return the level its on*)
(***********************************************************************************************************)
fun	depthSearch(LEAF (n)) comp = if n = comp then 1 else ~1
	| depthSearch(NODE (n, t1, t2)) comp = 
	let
		fun DSHelp x y = if x = y then 1 else ~1
	in
		if (depthSearch (t1) comp) <> ~1 then (depthSearch (t1) comp) + 1
		else if (depthSearch (t2) comp) <> ~1 then (depthSearch (t2) comp) + 1
		else if (DSHelp n comp) = 1 then 1
		else ~1
	end

(***********************************************************************************************************)
(*Question 5 C*)
(*This function adds two tree togethere, where there are nodes in both trees*)
(*it sums them up, if only a node from one tree exists, that node is simply put there*)
(***********************************************************************************************************)
fun	addTrees (LEAF (x)) (LEAF (y)) = LEAF(x+y)
	| addTrees (NODE (x, xt1, xt2)) (NODE (y, yt1, yt2))= NODE ((x + y), (addTrees (xt1) (yt1)), (addTrees (xt2) (yt2)))
	| addTrees (LEAF (x)) (NODE (y, yt1, yt2))= NODE ((x + y), (yt1), (yt2))
	| addTrees (NODE (x, xt1, xt2)) (LEAF (y))= NODE ((x + y), (xt1), (xt2));

(***********************************************************************************************************)
(*TESTS*)
(***********************************************************************************************************)
fun numbersToSumTest ()= 
	let
		val numbersToSumT1 = numbersToSum 100 [10, 20, 30, 40] = [10, 20, 30]
		val numbersToSumT2 = numbersToSum 30 [5, 4, 6, 10, 4, 2, 1, 5] = [5, 4, 6, 10, 4]
		val numbersToSumT3 = numbersToSum 1 [2] = []
		val numbersToSumT4 = numbersToSum 1 [] = []
		val numbersToSumT5 = numbersToSum 20 [5, 4, 5, 6, 8, 9, 10] = [5, 4, 5]
		val numbersToSumT6 = numbersToSum 1000 [1, 2, 3, 4] = [1, 2, 3, 4]
		val numbersToSumT7 = numbersToSum 0 [10, 20, 30, 40] = []
	in
		print ("---------QUESTION 1a----------- \n"   ^ 
			"numbersToSum:-------------------- \n"   ^ 
            "   test1: " ^ Bool.toString(numbersToSumT1) ^ "\n" ^ 
            "   test2: " ^ Bool.toString(numbersToSumT2) ^ "\n" ^  
			"   test3: " ^ Bool.toString(numbersToSumT3) ^ "\n" ^  
			"   test4: " ^ Bool.toString(numbersToSumT4) ^ "\n" ^  
			"   test5: " ^ Bool.toString(numbersToSumT5) ^ "\n" ^  
			"   test6: " ^ Bool.toString(numbersToSumT6) ^ "\n" ^  
			"   test7: " ^ Bool.toString(numbersToSumT7) ^ "\n" )
	end;

val _ =numbersToSumTest();

fun numbersToSumTailTest ()= 
	let
		val numbersToSumTailT1 = numbersToSumTail 100 [10, 20, 30, 40] = [10,20,30]
		val numbersToSumTailT2 = numbersToSumTail 30 [5, 4, 6, 10, 4, 2, 1, 5] = [5, 4, 6, 10, 4]
		val numbersToSumTailT3 = numbersToSumTail 1 [2] = []
		val numbersToSumTailT4 = numbersToSumTail 1 [] = []
		val numbersToSumTailT5 = numbersToSumTail 20 [5, 4, 5, 6, 8, 9, 10] = [5, 4, 5]
		val numbersToSumTailT6 = numbersToSumTail 1000 [1, 2, 3, 4] = [1, 2, 3, 4]
		val numbersToSumTailT7 = numbersToSumTail 0 [10, 20, 30, 40] = []
	in
		print ("---------QUESTION 1b----------- \n"   ^ 
			"numbersToSumTail:-------------------- \n"   ^ 
            "   test1: " ^ Bool.toString(numbersToSumTailT1) ^ "\n" ^ 
            "   test2: " ^ Bool.toString(numbersToSumTailT2) ^ "\n" ^  
			"   test3: " ^ Bool.toString(numbersToSumTailT3) ^ "\n" ^  
			"   test4: " ^ Bool.toString(numbersToSumTailT4) ^ "\n" ^  
			"   test5: " ^ Bool.toString(numbersToSumTailT5) ^ "\n" ^  
			"   test6: " ^ Bool.toString(numbersToSumTailT6) ^ "\n" ^  
			"   test7: " ^ Bool.toString(numbersToSumTailT7) ^ "\n" )
	end;

val _ =numbersToSumTailTest();	

fun partitionTest ()= 
	let
		val partitionT1 = partition (fn x => (x<=4)) [1,7,4,5,3,8,2,3] = ([1,4,3,2,3],[7,5,8])
		val partitionT2 = partition null [[1,2],[1],[],[5],[],[6,7,8]] = ([[],[]],[[1,2],[1],[5],[6,7,8]])
		fun exists n [] = false
			| exists n (x::rest) = if n=x then true else (exists n rest)
			
		val partitionT3 = partition (exists 1) [[1,2],[1],[],[5],[],[6,7,8]] = ([[1,2],[1]],[[],[5],[],[6,7,8]])
		val partitionT4 = partition (fn x=> (x<=4)) [] = ([],[])
		val partitionT5 = partition (fn x=> (x<=10)) [1, 2, 3, 4, 5, 6] = ([1, 2, 3, 4, 5, 6],[])
		val partitionT6 = partition (fn x=> (x<=0)) [1, 2, 3, 4, 5, 6] = ([],[1, 2, 3, 4, 5, 6])
	in
		print ("---------QUESTION 2----------- \n"   ^ 
			"partition:-------------------- \n"   ^ 
            "   test1: " ^ Bool.toString(partitionT1) ^ "\n" ^ 
            "   test2: " ^ Bool.toString(partitionT2) ^ "\n" ^  
			"   test3: " ^ Bool.toString(partitionT3) ^ "\n" ^
			"   test4: " ^ Bool.toString(partitionT4) ^ "\n" ^
			"   test5: " ^ Bool.toString(partitionT5) ^ "\n" ^
			"   test6: " ^ Bool.toString(partitionT6) ^ "\n" )
	end;

val _ = partitionTest();

fun areAllUniqueTest ()= 
	let
		val areAllUniqueT1 = areAllUnique [1,3,4,2,5,0,10] = true
		val areAllUniqueT2 = areAllUnique [[1,2],[3],[4,5],[]] = true
		val areAllUniqueT3 = areAllUnique [(1,"one"),(2,"two"),(1,"one")] = false
		val areAllUniqueT4 = areAllUnique [] = true
		val areAllUniqueT5 = areAllUnique [1,2,3,4,1,7] = false
		val areAllUniqueT6 = areAllUnique [1,1,1,1,1,1] = false
		val areAllUniqueT7 = areAllUnique [1,2] = true
		val areAllUniqueT8 = areAllUnique [(1,1),(1,1),(1,1)] = false
	in
		print ("---------QUESTION 3----------- \n"   ^ 
			"areAllUnique:-------------------- \n"   ^ 
            "   test1: " ^ Bool.toString(areAllUniqueT1) ^ "\n" ^ 
            "   test2: " ^ Bool.toString(areAllUniqueT2) ^ "\n" ^  
			"   test3: " ^ Bool.toString(areAllUniqueT3) ^ "\n" ^  
			"   test4: " ^ Bool.toString(areAllUniqueT4) ^ "\n" ^
			"   test5: " ^ Bool.toString(areAllUniqueT5) ^ "\n" ^
			"   test6: " ^ Bool.toString(areAllUniqueT6) ^ "\n" ^
			"   test7: " ^ Bool.toString(areAllUniqueT7) ^ "\n" ^
			"   test8: " ^ Bool.toString(areAllUniqueT8) ^ "\n")
	end;

val _ = areAllUniqueTest();

fun sumTest ()= 
	let
		val sumT1 = sum [[1,2,3],[4,5],[6,7,8,9],[]] = 45
		val sumT2 = sum [[10,10],[10,10,10],[10]] = 60
		val sumT3 = sum [[]] = 0
		val sumT4 = sum [] = 0
		val sumT5 = sum [[1],[1],[1],[1]] = 4
		val sumT6 = sum [[1,2,3,4,5,6]] = 21
		val sumT7 = sum [[100]] = 100
	in
		print ("---------QUESTION 4a----------- \n"   ^ 
			"sum:-------------------- \n"   ^ 
            "   test1: " ^ Bool.toString(sumT1) ^ "\n" ^ 
            "   test2: " ^ Bool.toString(sumT2) ^ "\n" ^  
			"   test3: " ^ Bool.toString(sumT3) ^ "\n" ^  
			"   test4: " ^ Bool.toString(sumT4) ^ "\n" ^
			"   test5: " ^ Bool.toString(sumT5) ^ "\n" ^
			"   test6: " ^ Bool.toString(sumT6) ^ "\n" ^
			"   test7: " ^ Bool.toString(sumT7) ^ "\n")
	end;

val _ = sumTest();

fun sumOptionTest ()= 
	let
		val sumOptionT1 = sumOption [[SOME(1),SOME(2),SOME(3)],[SOME(4),SOME(5)],[SOME(6),NONE],[],[NONE]] = SOME 21
		val sumOptionT2 = sumOption [[SOME(10),NONE],[SOME(10), SOME(10), SOME(10),NONE,NONE]] = SOME 40
		val sumOptionT3 = sumOption [[NONE]] = NONE
		val sumOptionT4 = sumOption [] = NONE
		val sumOptionT5 = sumOption [[NONE],[NONE],[NONE],[NONE]] = NONE
		val sumOptionT6 = sumOption [[NONE,NONE,NONE,NONE]] = NONE
		val sumOptionT7 = sumOption [[SOME(1)]] = SOME 1
	in
		print ("---------QUESTION 4b----------- \n"   ^ 
			"sumOption:-------------------- \n"   ^ 
            "   test1: " ^ Bool.toString(sumOptionT1) ^ "\n" ^ 
            "   test2: " ^ Bool.toString(sumOptionT2) ^ "\n" ^  
			"   test3: " ^ Bool.toString(sumOptionT3) ^ "\n" ^  
			"   test4: " ^ Bool.toString(sumOptionT4) ^ "\n" ^
			"   test5: " ^ Bool.toString(sumOptionT5) ^ "\n" ^
			"   test6: " ^ Bool.toString(sumOptionT6) ^ "\n" ^
			"   test7: " ^ Bool.toString(sumOptionT7) ^ "\n")
	end

val _ = sumOptionTest();

fun sumEitherTest ()= 
	let
		val sumEitherT1 = sumEither [[IString "1",IInt 2,IInt 3],[IString "4",IInt 5],[IInt 6,IString"7"],[],[IString "8"]] = IInt 36
		val sumEitherT2 = sumEither [[IString "10" , IInt 10],[],[IString "10"],[]] = IInt 30
		val sumEitherT3 = sumEither [[]] = IInt 0
		val sumEitherT4 = sumEither [[IString "6"]] = IInt 6
		val sumEitherT5 = sumEither [[IInt 6]] = IInt 6
		val sumEitherT6 = sumEither	[[IString "6"],[IString "6"],[IString "6"]] = IInt 18
		val sumEitherT7 = sumEither [[IInt 6],[IInt 6],[IInt 6]] = IInt 18
	in
		print ("---------QUESTION 4c----------- \n"   ^ 
			"sumEither:-------------------- \n"   ^ 
            "   test1: " ^ Bool.toString(sumEitherT1) ^ "\n" ^ 
            "   test2: " ^ Bool.toString(sumEitherT2) ^ "\n" ^  
			"   test3: " ^ Bool.toString(sumEitherT3) ^ "\n" ^  
			"   test4: " ^ Bool.toString(sumEitherT4) ^ "\n" ^
			"   test5: " ^ Bool.toString(sumEitherT5) ^ "\n" ^
			"   test6: " ^ Bool.toString(sumEitherT6) ^ "\n" ^
			"   test7: " ^ Bool.toString(sumEitherT7) ^ "\n")
	end

val _ = sumEitherTest();

fun depthScanTest ()= 
	let
		val depthScanT1 = depthScan (NODE("Science",NODE ("and",LEAF "School", NODE("Engineering", LEAF "of",LEAF "Electrical")),LEAF "Computer")) = ["School","of","Electrical","Engineering","and","Computer","Science"]
		val depthScanT2 = depthScan (NODE(1, NODE (2, NODE(3, LEAF 4 ,LEAF 5),LEAF 6), NODE(7,LEAF 8,LEAF 9))) = [4,5,3,6,2,8,9,7,1]
		val depthScanT3 = depthScan (LEAF 4) = [4]
		val depthScanT4 = depthScan (NODE(6, NODE(4, NODE(2,LEAF 1,LEAF 3),LEAF 5),LEAF 7)) = [1,3,2,5,4,7,6]
		val depthScanT5 = depthScan (NODE(3, LEAF 1,LEAF 5)) = [1,5,3]
		val depthScanT6 = depthScan	(NODE(4, NODE(2,LEAF 1,LEAF 3),LEAF 5)) = [1,3,2,5,4]
	in
		print ("---------QUESTION 5a----------- \n"   ^ 
			"depthScan:-------------------- \n"   ^ 
            "   test1: " ^ Bool.toString(depthScanT1) ^ "\n" ^ 
            "   test2: " ^ Bool.toString(depthScanT2) ^ "\n" ^  
			"   test3: " ^ Bool.toString(depthScanT3) ^ "\n" ^  
			"   test4: " ^ Bool.toString(depthScanT4) ^ "\n" ^
			"   test5: " ^ Bool.toString(depthScanT5) ^ "\n" ^
			"   test6: " ^ Bool.toString(depthScanT6) ^ "\n")
	end

val _ = depthScanTest();

fun depthSearchTest ()= 
	let
		val myT = NODE(1, NODE (2, NODE(3, LEAF 2 ,LEAF 5),LEAF 1), NODE(1,LEAF 8,LEAF 5))

		val depthSearchT1 = depthSearch myT 1 = 3
		val depthSearchT2 = depthSearch myT 5 = 4
		val depthSearchT3 = depthSearch myT 8 = 3
		val depthSearchT4 = depthSearch myT 4 = ~1
	in
		print ("---------QUESTION 5b----------- \n"   ^ 
			"depthSearch:-------------------- \n"   ^ 
            "   test1: " ^ Bool.toString(depthSearchT1) ^ "\n" ^ 
            "   test2: " ^ Bool.toString(depthSearchT2) ^ "\n" ^  
			"   test3: " ^ Bool.toString(depthSearchT3) ^ "\n" ^  
			"   test4: " ^ Bool.toString(depthSearchT4) ^ "\n")
	end

val _ = depthSearchTest();

fun addTreesTest ()= 
	let
		val T1 = NODE(1, NODE (2, NODE(3, LEAF 4 ,LEAF 5),LEAF 6), NODE(7,LEAF 8,LEAF 9))
		val T2 = NODE(1, NODE (2, LEAF 3, LEAF 6), NODE(7, NODE(8, LEAF 10 ,LEAF 11),LEAF 9))
		
		val addTreesT1 = addTrees T1 T2 = NODE (2,NODE (4,NODE (6,LEAF 4,LEAF 5),LEAF 12), NODE (14,NODE (16,LEAF 10,LEAF 11),LEAF 18))
	in
		print ("---------QUESTION 5c----------- \n"   ^ 
			"addTrees:-------------------- \n"   ^ 
            "   test1: " ^ Bool.toString(addTreesT1) ^ "\n")
	end

val _ = addTreesTest();

fun TreeTest ()= 
	let
		val T1 = NODE(8, NODE(6, NODE(4, NODE (2,LEAF (1),LEAF (3)),LEAF (5)),LEAF (7)),LEAF (9));
		val T2 = NODE(2,LEAF (1), NODE(4,LEAF (3), NODE(6,LEAF (5), NODE (8,LEAF (7),LEAF (9)))));
		val T3 = NODE(85, NODE(71, NODE(21, NODE (30,LEAF (10),LEAF (15)),LEAF (36)), NODE (37,LEAF (91),LEAF (59))), NODE(76,LEAF (1), NODE(35,LEAF (36),LEAF (13))));
		val depthScanT1 = depthScan T1 = [1,3,2,5,4,7,6,9,8]
		val depthScanT2 = depthScan T2 = [1,3,5,7,9,8,6,4,2]
		val depthScanT3 = depthScan T3 = [10,15,30,36,21,91,59,37,71,1,36,13,35,76,85]
		val depthSearchT11 = depthSearch T1 5 = 4
		val depthSearchT12 = depthSearch T1 8 = 1
		val depthSearchT21 = depthSearch T2 10 = ~1
		val depthSearchT22 = depthSearch T2 3 = 3
		val depthSearchT31 = depthSearch T3 59 = 4
		val depthSearchT32 = depthSearch T3 36 = 4
		val addTreesT1 = addTrees T1 T2 = NODE (10,NODE (7,NODE (4,NODE (2,LEAF 1,LEAF 3),LEAF 5),LEAF 7), NODE (13,LEAF 3,NODE (6,LEAF 5,NODE (8,LEAF 7,LEAF 9))))
		val addTreesT2 = addTrees T2 T3 = NODE (87,NODE (72,NODE (21,NODE (30,LEAF 10,LEAF 15),LEAF 36),NODE (37,LEAF 91,LEAF 59)),NODE (80,LEAF 4,NODE (41,LEAF 41,NODE (21,LEAF 7,LEAF 9))))
		val addTreesT3 = addTrees T3 T1 = NODE (93,NODE (77,NODE (25,NODE (32,LEAF 11,LEAF 18),LEAF 41), NODE (44,LEAF 91,LEAF 59)),NODE (85,LEAF 1,NODE (35,LEAF 36,LEAF 13)))
	in
		print ("---------QUESTION 5 GENERAL TESTING----------- \n"   ^ 
			"depthScans:-------------------- \n"   ^ 
            "   test1: " ^ Bool.toString(depthScanT1) ^ "\n" ^ 
            "   test2: " ^ Bool.toString(depthScanT2) ^ "\n" ^  
			"   test3: " ^ Bool.toString(depthScanT3) ^ "\n" ^ 
			"depthSearchs:-------------------- \n"   ^ 
            "   test1: " ^ Bool.toString(depthSearchT11) ^ "\n" ^ 
            "   test2: " ^ Bool.toString(depthSearchT12) ^ "\n" ^  
			"   test3: " ^ Bool.toString(depthSearchT21) ^ "\n" ^ 
            "   test4: " ^ Bool.toString(depthSearchT22) ^ "\n" ^ 
            "   test5: " ^ Bool.toString(depthSearchT31) ^ "\n" ^  
			"   test6: " ^ Bool.toString(depthSearchT32) ^ "\n" ^
			"addTrees:-------------------- \n"   ^ 
            "   test1: " ^ Bool.toString(addTreesT1) ^ "\n"^ 
            "   test2: " ^ Bool.toString(addTreesT2) ^ "\n"^ 
            "   test3: " ^ Bool.toString(addTreesT3) ^ "\n")
	end

val _ = TreeTest();