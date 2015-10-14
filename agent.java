import java.io.*;
import java.util.*;
class Clause
{
	 Sentence lhs[];
	 Sentence conclusion;
	 LinkedList<Clause> collisionList=new LinkedList<Clause>();
	 public Clause()
	 {
		 conclusion=new Sentence();
	 }
	 public Clause(Clause temp)
	 {
		 if(temp.lhs!=null)
		 {
			 lhs = new Sentence[temp.lhs.length];
		 for(int i=0;i<temp.lhs.length;i++)
			 lhs[i] = new Sentence(temp.lhs[i]);
		 }
		 if(temp.conclusion!= null)
		 conclusion = new Sentence(temp.conclusion);
		 collisionList = new LinkedList<Clause>(temp.collisionList);
		 
	 }
	 public Clause(Sentence conclusion)
	 {
		 this.conclusion= new Sentence(conclusion);
	 }
	 public String toString()
	 {
		 if(lhs!=null)
		 for(int i=0;i<lhs.length;i++)
			 System.out.println(lhs[i]);
		 return ("conclusion="+conclusion);
	 }
	 public boolean equals(Object obj)
	 {
		 Clause temp = (Clause) obj;
		 if(temp.conclusion.arg1.equals(conclusion.arg1) && temp.conclusion.predicate.equals(conclusion.predicate)  )
		 {
			 if(temp.conclusion.arg2 != null)
			 { if(temp.conclusion.arg2.equals(conclusion.arg2)) return true;
			 else return false;
			 }
			 
		 }
		 else return false;
		 return false;
	 }

}
class Sentence  
{
	String predicate=null;
	String arg1=null;
	String arg2=null;
	public Sentence()
	{
		
	}
	public Sentence (Sentence copy)
	{
		predicate = new String (copy.predicate);
		if(copy.arg1!=null)
		arg1 = new String (copy.arg1);
		if(copy.arg2!= null)
		arg2 = new String (copy.arg2);
	}
	public String toString()
	{
		String toBeSent="predicate="+predicate+" arg1="+arg1+" arg2="+arg2;
		return toBeSent;
	}
	
}
public class agent 
	{
		public static void main(String args[])
			{
				new backwardChaining();
		
			}

	}
class backwardChaining
	{
	private BufferedReader bf;
	private int noOfClauses;
	private String result;
	private boolean entailment=false;
	private boolean foundX = false;
	private Clause startClause = null;
	private int forToBeExcluded = 0;
	private String substitution; /*Since it is gauranteed that there will be only one variable, we can use one global variable for this*/
	String valueOfX;
	Clause clause[];
	LinkedList<Clause> toBeExcluded= new LinkedList<Clause> ();
	Hashtable<String, Clause> KB = new Hashtable<String , Clause>();
	Clause query=new Clause();
		public backwardChaining()
			{
				input();
				fillTable();
				output();
				entailment=fol_bc_ask();
				if(entailment == false && startClause!=null)
				{
					forToBeExcluded++;
					input();
					KB = new Hashtable<String , Clause>();
					fillTable();
					valueOfX = null;
					entailment = fol_bc_ask();
				}
			//	System.out.println("The value of x to be replaced="+valueOfX);
			//	System.out.println("Value of lookup = "+entailment);
				write();
			}
		private void write() {
			// TODO Auto-generated method stub
			try{
				
			String fileName="output.txt";
			PrintWriter pw=new PrintWriter(new BufferedWriter(new FileWriter(fileName,false)));
			if(entailment == false)
			pw.println("FALSE");
			else 
				pw.println("TRUE");
			pw.close();
			}catch(Exception E)
			{
				//System.out.println("Exception found in e:"+E);
			}
		}
		private boolean fol_bc_ask() {
			// TODO Auto-generated method stub
		
			boolean decision=false;
			startClause=findLhsForGoal(clause[0]);   /*At this point, you would have got either null or a valid clause*/
			if(startClause == null)
			return false;
			if(valueOfX == null)
			{
				/*It means that we still have to find a valid substitution for x*/
				/*for(int i=0;i<startClause.lhs.length;i++)
				{
					
					Clause next = findLhsForGoal(new Clause(startClause.lhs[i]));
					if(valueOfX != null) {
						System.out.println("GOt x");
						break;
					}
					
				}
				
*/				Clause nex = resolveRecurssively(startClause);
				if(nex == null) return false;
			//	System.out.println("value of x="+ valueOfX);
			}
			//System.out.println("Value of x is found to be ="+ valueOfX);
			if(valueOfX == null)
			return false;
			return lookup(startClause);
			
			/*Remaining logic for the DFS to be written.. Depending upon further examples.*/
			/*Clause answer = resolveRecurssively(startClause);
			
			if(answer == null)
			return decision;
			else return true;*/
		}
		private boolean lookup(Clause goal) {
			
			
			boolean finalV = false;
			if(goal.lhs == null) return true;
			for(int i=0;i<goal.lhs.length;i++)
			{
				replaceX(goal.lhs[i]);
				{
					toBeExcluded.add(new Clause(goal.lhs[i]));
					
				}
				Clause temp = KB.get(goal.lhs[i].predicate);
				/*if(temp != null)
				{
				Clause uCheck = unify(new Clause(goal.lhs[i]),new Clause(temp));
				if(uCheck != null)
					System.out.println("value of x:"+valueOfX);
				}*/
				if(temp!=null)
				replaceX(temp.conclusion);
				if(temp == null || compare(new Clause(goal.lhs[i]),new Clause(temp.conclusion),-1) == false)
				{
					/*Look it up in the collision chain*/
					Clause temp1 = null;
					if(temp.collisionList.isEmpty()) return false;
					for(int j=0;j<temp.collisionList.size();j++)
					{
						temp1=temp.collisionList.get(j);
						if(temp1 == null) return false;
						Clause modified = unify(new Clause(goal.lhs[i]),temp1);
						if(modified != null)
						{
							if(temp1.conclusion.arg1.equals("x")) temp1.conclusion.arg1 = goal.lhs[i].arg1;
							else if(temp1.conclusion.arg2!=null)
							{
								if(temp1.conclusion.arg2.equals("x")) temp1.conclusion.arg2 = goal.lhs[i].arg2;

							}
							break;
							
						}
						replaceX(temp1.conclusion);
						if(compare(new Clause(goal.lhs[i]),new Clause(temp1.conclusion),-1) == true) break;
						
					}
					temp = temp1;
				}
				
				if(compare(new Clause(goal.lhs[i]),new Clause(temp.conclusion),-1) == false) return false;
				finalV= lookup(temp);
				if(finalV == false) return false;
	
			}
			return true;
		}
		private void replaceX(Sentence sentence) {
			// TODO Auto-generated method stub
			if(sentence.arg1.equals ("x")) 
				sentence.arg1 = valueOfX;
			if(sentence.arg2 != null)
			if(sentence.arg2.equals("x")) sentence.arg2 = valueOfX;
			
		}
		private Clause findClause(Sentence sentence) {
			// TODO Auto-generated method stub
			return KB.get(sentence.predicate);
			
		}
		private Clause resolveRecurssively(Clause startClause) {
			// TODO Auto-generated method stub
			Clause next = null;
			if(startClause.lhs == null) return null;
			for(int i=0;i<startClause.lhs.length;i++)
			{
				next = findLhsForGoal(new Clause(startClause.lhs[i]));
				if(next == null) return null;
			if(valueOfX != null) {
				//System.out.println("GOt x");
				return next;
			}

				return resolveRecurssively(next);
			}
			return next;
		}
		private Clause findLhsForGoal(Clause goal) {
			// TODO Auto-generated method stub
			Clause toBeReturned=null;
			if((toBeReturned=KB.get(goal.conclusion.predicate))==null)
			return null;
			else
			{
				/*Check if it can be unified
				 * if not, check if there is a collision list.
				 * if it is not null, then follow it and check every node and see if they can be unified with the goal.
				 * if everything fails, return null*/
				Clause ret;
				ret=unify(goal,toBeReturned);
				if(ret == null)
				{
					if(toBeReturned.collisionList.isEmpty()) return null;
					for(int i=0;i<toBeReturned.collisionList.size();i++)
					{
						Clause temp=toBeReturned.collisionList.get(i);
						if(unify(goal,temp)==temp) return temp;
					}
					/*Must go through the linked list*/
				}
				else return toBeReturned; /*If a valid reference is returned, then it means that it has been unified and can be returned*/
				
			}
			return null;
		}
		private Clause unify(Clause goal, Clause toBeReturned) {
			// TODO Auto-generated method stub
			int argc=0;
			int pos=1;
			if(goal.conclusion.arg2!=null) argc=2;
			else argc=1;
			boolean rv = compare(goal,toBeReturned,argc);
			if(rv == true) return toBeReturned;
			if(!toBeReturned.conclusion.arg1.equals("x") && !toBeReturned.conclusion.arg1.equals(goal.conclusion.arg1)) /*The first argument has to be a variable*/
			if(goal.conclusion.arg1.equals("x"))
			{
				if(argc == 2)
				{
				if(toBeReturned.conclusion.arg2.equals(goal.conclusion.arg2))
				{
					if(valueOfX==null)
					{
					valueOfX = new String(toBeReturned.conclusion.arg1);
					foundX = true;
					}
					return toBeReturned;
				}
				}
				else 
				{
					if(valueOfX == null)
					{
					valueOfX = new String(toBeReturned.conclusion.arg1);
					foundX = true;
					}
					return toBeReturned;
				}
				return null;
			}
			else return null;
			if(argc == 2)
			if(goal.conclusion.arg2.equals("x"))
			{	
				if(!goal.conclusion.arg1.equals(toBeReturned.conclusion.arg1)) return null;
				if(valueOfX == null)
				{
				valueOfX = new String(toBeReturned.conclusion.arg2);
				foundX = true;
				}
				return toBeReturned;
			}
			if(argc==2)
			{
				/*If the control comes here, then it means that both the arguments of the sentence in arg1 are equal and are constants*/
			if(goal.conclusion.arg1.equals(goal.conclusion.arg2)) /*If both the arguments in the conclusion are equal.*/
			if(!(toBeReturned.conclusion.arg1.equals("x") && toBeReturned.conclusion.arg2.equals("x"))) return null;	/*Then both the arguments in the toBeReturned have to be x*/
			if(toBeReturned.conclusion.arg1.equals("x") && !toBeReturned.conclusion.arg2.equals(goal.conclusion.arg2)) return null;
			if(!toBeReturned.conclusion.arg2.equals("x") && !toBeReturned.conclusion.arg2.equals(goal.conclusion.arg2))
					return null;
				
			}
			if(toBeReturned.conclusion.arg1.equals("x")) 
				if(valueOfX == null)
				{
				valueOfX=new String(goal.conclusion.arg1);
				foundX = true;
				}
			if(argc==2)
				if(toBeReturned.conclusion.arg2.equals("x")) 
					if(valueOfX == null)
				{
						foundX = true;
					valueOfX=new String(goal.conclusion.arg2);
				}
			/*If the control comes here, then it means that these two sentences can be unified*/
			return toBeReturned;
		}
		private boolean compare(Clause goal, Clause toBeReturned, int argc) {
			// TODO Auto-generated method stub
			if(argc == -1) 
			{
				int tempc= 0;
				/*Caluclate argument count yourself*/
				if(goal.conclusion.arg2 == null)
				{
					if(toBeReturned.conclusion.arg2 == null)
					{
						argc = 1;
					}
					else return false;
				}
				else argc =2;
			}
			if(!goal.conclusion.arg1.equals(toBeReturned.conclusion.arg1))  return false;
			if(argc == 2)
			{
				/*At this point, first argument is the same*/
				if(!goal.conclusion.arg2.equals(toBeReturned.conclusion.arg2))  return false;
			}
			/*If the control comes here, then it means that both the arguments are equal.*/
			return true;
		}
		private void fillTable() 
		{
			// TODO Auto-generated method stub
			int temp =0;
			for(int i=1;i<clause.length;i++)
			{
				if(exists(clause[i])==true) 
					{
					if(!(temp++ >= forToBeExcluded))
					continue;
					}
				if(KB.containsKey(clause[i].conclusion.predicate)){
					KB.get(clause[i].conclusion.predicate).collisionList.add(clause[i]);
					//System.out.println("Added");
					//System.out.println(KB.get(clause[i].conclusion.predicate).collisionList.getFirst().toString());
				}
				else
				KB.put(clause[i].conclusion.predicate, clause[i]);
			}
			
		}
		private boolean exists(Clause clause2) {
			// TODO Auto-generated method stub
			for(int i=0;i<toBeExcluded.size();i++)
			{
				if(toBeExcluded.get(i).equals(clause2)) return true;
			}
				return false;
		}
		private void output() 
			{
		// TODO Auto-generated method stub0
			//	System.out.println("result="+result);
					for(int i=0;i<noOfClauses+1;i++)
					{
						//.out.println(clause[i]);
					}
				//System.out.println("Different types of predicates in the KB are:");
				//System.out.println(KB.keySet());
		
			}
private void input()
	{
	int lineCount=0;
	try{
		String line;
		int i=0;
		 bf=new BufferedReader(new FileReader("input.txt"));    /*REMEMBER TO CHANGE IT BEFORE SUBMISSION*/
			while((line=bf.readLine())!=null)
			{
				if(lineCount==0) {
					result=line;
					
				}
				else if(lineCount==1)
				{
				noOfClauses=Integer.parseInt(line);
				clause=new Clause[noOfClauses+1];
					for(int tempo=0;tempo<noOfClauses+1;tempo++)
						clause[tempo]=new Clause();
						parseClause(result,i++);
				}
				else
				{
					
					parseClause(line,i++);
					//System.out.println("Calling on "+line);
				}
				lineCount++;

				
			}
		}catch(IOException e)
		{
			System.out.println("Error occured="+e);
		}

	}
private void parseClause(String clauseS,int i)
{
	// TODO Auto-generated method stub
	try
	{
	int j=0;
	if(!clauseS.contains("=>"))
		{
		
			clause[i].conclusion=new Sentence();
			clause[i].conclusion.predicate=clauseS.substring(0,clauseS.indexOf("("));
			if(!clauseS.contains(","))
			{	/*If there is only one argument*/
				clause[i].conclusion.arg1=clauseS.substring(clauseS.indexOf("(")+1, clauseS.length()-1);
				
			}
			else
			{
				/*If there are two arguments*/
				String temp;
				clause[i].conclusion.arg1=clauseS.substring(clauseS.indexOf("(")+1,clauseS.indexOf(","));
				clause[i].conclusion.arg2=clauseS.substring(clauseS.indexOf(",")+1,clauseS.indexOf(")"));
			
			}
		}
	else
	{
		/*If the control comes here then it means that the clause has both 
		 * lhs and rhs.*/
		String lhs[]=clauseS.substring(0,clauseS.indexOf(">")).split("&");
		clause[i].lhs=new Sentence[lhs.length];
		for(int tempo=0;tempo<lhs.length;tempo++)
			clause[i].lhs[tempo]=new Sentence();
		for(j=0;j<lhs.length;j++)
			{
				clause[i].lhs[j].predicate=lhs[j].substring(0,lhs[j].indexOf("("));
				if(!lhs[j].contains(","))
				{
					clause[i].lhs[j].arg1=lhs[j].substring(lhs[j].indexOf("(")+1, lhs[j].indexOf(")"));
					
				}
				else
				{
					/*If there are two arguments*/
					clause[i].lhs[j].arg1=lhs[j].substring(lhs[j].indexOf("(")+1,lhs[j].indexOf(","));
					clause[i].lhs[j].arg2=lhs[j].substring(lhs[j].indexOf(",")+1,lhs[j].indexOf(")"));
					
				}


			}
	/*Code for the result part has to go here*/
		String result=clauseS.substring(clauseS.indexOf(">")+1,(clauseS.length()));
		clause[i].conclusion.predicate=result.substring(0,result.indexOf("("));
		if(!result.contains(","))
		{
			clause[i].conclusion.arg1=result.substring(result.indexOf("(")+1,result.indexOf(")"));
			
		}
		else
		{
			/*If there are two arguments*/
			clause[i].conclusion.arg1=result.substring(result.indexOf("(")+1,result.indexOf(","));
			clause[i].conclusion.arg2=result.substring(result.indexOf(",")+1,result.indexOf(")"));
			
		}
		
	}
	}catch(Exception E)
	{
		System.out.println("Exception found while parsing the clause and the cause error="+E);
	}
	
	
}


}