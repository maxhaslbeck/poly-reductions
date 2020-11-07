\<^marker>\<open>creator "Max Haslbeck"\<close>
\<^marker>\<open>contributor "Simon Wimmer"\<close>
chapter \<open>Sketch of the Cook Levin Theorem\<close>
theory Cook_Levin
  imports Main Polynomial_Growth_Functions Three_Sat_To_Set_Cover
begin

paragraph \<open>Summary\<close>
text \<open>This theory sketches the Cook Levin Theorem.\<close>

section \<open>IMP-\<close>

type_synonym register = string
type_synonym val = nat
type_synonym state = "register \<Rightarrow> val"

datatype
  com = SKIP 
    (*  | Assign vname aexp       ("_ ::= _" [1000, 61] 61) *)
      | Seq    com  com         ("_;;/ _"  [60, 61] 60)
      | If     register com com     ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
      | While  register com         ("(WHILE _/ DO _)"  [0, 61] 61)

subsection \<open>Semantic\<close>

inductive
  big_step_t :: "com \<times> state \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> bool"  ("_ \<Rightarrow> _ \<Down> _" 55)
where
Skip: "(SKIP,s) \<Rightarrow> Suc 0 \<Down> s" |
(* Assign: "(x ::= a,s) \<Rightarrow> Suc 0 \<Down> s(x := aval a s)" | *)
Seq: "\<lbrakk> (c1,s1) \<Rightarrow> x \<Down> s2;  (c2,s2) \<Rightarrow> y \<Down> s3 ; z=x+y \<rbrakk> \<Longrightarrow> (c1;;c2, s1) \<Rightarrow> z \<Down> s3" |
IfTrue: "\<lbrakk> s r \<noteq> 0;  (c1,s) \<Rightarrow> x \<Down> t; y=x+1 \<rbrakk> \<Longrightarrow> (IF r THEN c1 ELSE c2, s) \<Rightarrow> y \<Down> t" |
IfFalse: "\<lbrakk> s r = 0;  (c2,s) \<Rightarrow> x \<Down> t; y=x+1  \<rbrakk> \<Longrightarrow> (IF r THEN c1 ELSE c2, s) \<Rightarrow> y \<Down> t" |
WhileFalse: "\<lbrakk> s r = 0 \<rbrakk> \<Longrightarrow> (WHILE r DO c,s) \<Rightarrow> Suc 0 \<Down> s" |
WhileTrue: "\<lbrakk> s1 r \<noteq> 0;  (c,s1) \<Rightarrow> x \<Down> s2;  (WHILE r DO c, s2) \<Rightarrow> y \<Down> s3; 1+x+y=z  \<rbrakk> 
    \<Longrightarrow> (WHILE r DO c, s1) \<Rightarrow> z \<Down> s3"




fun vars :: "com \<Rightarrow> register set" where
  "vars SKIP = {}"
|  "vars (c1;;c2) = vars c1 \<union> vars c2"

(* TODO: define small step semantics *)

fun small_step_t where
  "small_step_t (c,s) (c',s') = undefined"

(* TODO: prove equivalence of small step and big step semantics *)

(* TODO: define functions that extract the running time and
    result of a program p that terminates after being started from state s *)

definition "time x = undefined"

definition "result x = undefined"

lemma 
  assumes "(c,s) \<Rightarrow> t \<Down> s'"
  shows "result (c,s) = s' ''r''" (* we define the r register to be the "result" *)
  sorry

lemma 
  assumes "(c,s) \<Rightarrow> t \<Down> s'"
  shows "time (c,s) = t"
  sorry



subsection \<open>Bound on Registers from bound on computation steps\<close>


text \<open>If the inputs of a IMP- computation is bounded by x, and the running time is polynomial
    in x, then all result registers have size at most\<close>

theorem regististers_poly_if_time_poly:
assumes 
  "poly T"
  "\<forall>r. s r \<le> x"
  "(c,s) \<Rightarrow> t \<Down> s'"
  "t \<le> T x"
shows
  "\<exists>p. poly p \<and> (\<forall>r. s' r \<le> p x)"
  sorry

(* this only implies that the result is not too big
  we need a small step semantics, to make sure that no intermediate register is too large *)



locale SAT_encoding =
  fixes enc_formula :: "nat three_sat \<Rightarrow> nat"
  and   enc_program :: "com \<Rightarrow> nat"            
  and   enc_pair :: "(nat * nat) \<Rightarrow> nat"                        
begin


section \<open>P - deterministic polynomial computation\<close>

definition depends_on_input where
  "depends_on_input P \<equiv> (\<forall>s1 s1' t s2. s1 ''x'' = s2 ''x'' \<longrightarrow> ((P,s1) \<Rightarrow> t \<Down> s1')
                                  \<longrightarrow> (\<exists>s2'. ((P,s2) \<Rightarrow> t \<Down> s2') \<and> s1' ''r'' = s2' ''r''))"

definition wf_com where
  "wf_com \<equiv> {P. depends_on_input P}"


definition len :: "nat \<Rightarrow> nat" where "len x = undefined"

definition P where
  "P = {D. \<exists>P\<in>wf_com. 
            (\<exists>p_t. poly p_t \<and>
               (\<forall>x.
                  (x\<in>D \<longleftrightarrow> (\<exists>t s s'. s ''x'' = x \<and> (P,s) \<Rightarrow> t \<Down> s' \<and> t \<le> p_t (len x) \<and> s' ''r'' = 1))))
        }" 


section \<open>NP - nondeterministic polynomial computation\<close>


(* first attempt to define NP, from intuition *)
definition NP where
  "NP = {D. \<exists>P\<in>wf_com.
               (\<exists>p_t p_c. poly p_t \<and> poly p_c \<and>
                  (\<forall>x. x \<in> D
                     \<longleftrightarrow> (\<exists>c. len c \<le> p_c x \<and> 
                            (\<forall>s. s ''x'' = enc_pair (x,c)
                                 \<longrightarrow> (\<exists>t s'. (P,s) \<Rightarrow> t \<Down> s' \<and> t \<le> p_t (len (enc_pair (x,c))) \<and> s' ''r'' = 1) 
                            )
                         )
                  )
                )
        }"

lemma deterministic: "(c, s) \<Rightarrow> t1 \<Down> s1' \<Longrightarrow> (c, s) \<Rightarrow> t2 \<Down> s2' \<Longrightarrow> t1 = t2 \<and> s1' = s2'"
  sorry



lemma depends_on_inputD:
  assumes  "depends_on_input c"
  shows "\<And>s1 s1' t1 t2 s2 s2'. s1 ''x'' = s2 ''x'' \<Longrightarrow> ((c,s1) \<Rightarrow> t1 \<Down> s1')
                      \<Longrightarrow> (\<exists>t2 s2'. ((c,s2) \<Rightarrow> t2 \<Down> s2') \<and> t1 = t2 \<and>  s1' ''r'' = s2' ''r'')"
  using assms unfolding depends_on_input_def 
  using deterministic  by blast
  
(*  Attempt to define NP using the definition of P
  apparently the rhs is stronger, it implies the lhs,
  but I could not yet show equivalence
 *)
lemma "D \<in> NP \<longleftrightarrow> (\<exists>D\<^sub>C\<in>P. (\<exists>p_c. poly p_c \<and> (\<forall>x. x\<in>D \<longleftrightarrow> (\<exists>c. len c \<le> p_c x \<and> enc_pair(x,c) \<in> D\<^sub>C))))"
  unfolding NP_def P_def 
  apply simp
  apply safe
  subgoal for P p_t p_c
    \<comment> \<open>\<open>P\<close> is the decision procedure.
        The decision problem is trivially \<open>D_P\<close>, the set accepted by \<open>P\<close>\<close>
    apply (rule exI[where x =
          "{n. \<exists>s t s'. s ''x'' = n \<and> (P, s) \<Rightarrow> t \<Down> s' \<and> t \<le> p_t (len n) \<and> s' ''r'' = 1}"])
    apply safe
    subgoal \<comment> \<open>Show that \<open>D_P\<close> is decided by \<open>P\<close>\<close>
      apply fastforce
      done
    apply clarsimp
    apply (rule exI[where x = p_c], clarsimp)
    apply safe
    subgoal for x c
      apply (rule exI[where x = c], rule conjI, assumption)
      apply (rule exI[where x = "(\<lambda>_. undefined)(''x'' := enc_pair (x, c))"])
      apply auto
      done
    subgoal for x c s t s'
      apply (rule exI[where x = c], rule conjI, assumption)
      apply auto
      subgoal premises p for s1 \<comment> \<open>The definition of @{term depends_on_input} is too weak:
        we are missing termination\<close>
        using p(1)[unfolded wf_com_def, simplified, THEN depends_on_inputD, of s s1, simplified p(6,10), OF _ p(7)]
        apply auto subgoal for s2'
          apply(rule exI[where x=t])
          apply(rule exI[where x=s2'])
          using p by auto
        done
      done
    done
  subgoal premises prems for D\<^sub>C P p_c p_t
    apply(rule bexI[where x=P])
     apply(rule exI[where x=p_t])
     apply(simp_all add: prems)
    apply(rule exI[where x=p_c]) 
    apply(simp_all add: prems)
    apply(rule) 
    subgoal for x
      apply rule
      subgoal apply safe subgoal for c t s s' apply(rule exI[where x= c]) apply simp
        apply safe  subgoal premises p for s1
          \<comment> \<open>Again, we are missing termination in @{term depends_on_input}\<close>
          using prems(1)[unfolded wf_com_def, simplified, THEN depends_on_inputD, of s s1, simplified p(2,6), OF _ p(3)]
          apply auto 
          subgoal for s2' apply(rule exI[where x=t]) apply(rule exI[where x=s2']) using prems p by auto
          done
        done
      done
    subgoal apply safe subgoal for c apply(rule exI[where x=c])
      apply simp
      subgoal premises prem2
        using 
          prem2(2)[rule_format, of "0(''x'':=enc_pair(x,c))"]
        apply auto
        subgoal for t s'
          apply (rule exI[where x = t], rule exI[where x = "0(''x'':=enc_pair(x,c))"])
          apply auto
          done
        done
      done
    done
  done
  done
  done


(* idee man könnte als convention machen,
  dass ''x'' immer ein paar (x,F) aus input und Frame ist
  und ein wohlgeformtes program das ergebnis c, zusammen mit dem Frame F
  in das result register packt ''r'' := (r,F)  
  ausserdem, das ergebnis nur von x und nicht von F abhängt.
  somit könnte man IMP- sehr allgemein lassen, aber mit wohlgeformtheits annahmen doch einige
  konventionen und eigenschaften der Programme voraussetzen.
*)
 

subsection \<open>"Close the circle": poly reductions\<close>


definition IMP_reduction (infix "\<le>\<^sub>I" 50) where
  "D \<le>\<^sub>I D' \<equiv>
   (\<exists>p. poly p \<and> 
     (\<exists>f::com.
       (\<forall>x. time (f, x) \<le> p(size(x))
        \<and>  (x \<in> D \<longleftrightarrow> (result (f,x) ) \<in> D'))))"

lemma IMP_reduction_alt:
  "D \<le>\<^sub>I D' =
   (\<exists>p. poly p \<and> 
     (\<exists>f::com.
       (\<forall>x. ((\<forall>s. s ''x'' = x \<longrightarrow> (\<exists>t s'. (f,s) \<Rightarrow> t \<Down> s' \<and> t \<le> p(size(x)) \<and> (s' ''r'' \<in> D' \<longleftrightarrow> x \<in> D)))))))"
  sorry
 
(* TODO: define NP hard *)

definition "NP_hard D = (\<forall>D'\<in>NP. D' \<le>\<^sub>I D)"

(* TODO: define NP-complete *)

text \<open>A problem in B in NP is NP-complete if, for any problem in NP, there is a polynomial-time reduction from A to B\<close>

definition "NP_complete D = undefined"


definition decode_pair :: "_\<Rightarrow>_\<Rightarrow>_\<Rightarrow>com" where
  "decode_pair S a b = undefined"

lemma decode_pair_correct:
  "finite S \<Longrightarrow> (\<forall>s. s ''x'' = enc_pair (x, y) \<longrightarrow> 
    (\<exists>t s'. (decode_pair S a b,s) \<Rightarrow> t \<Down> s' \<and> s' a = x \<and> s' b = y \<and> (\<forall>v\<in>S. s' v = s v)))"
  sorry
lemma decode_pair_correct':
  "(s ''x'' = enc_pair (x, y) \<Longrightarrow> 
    (\<exists>t s'. (decode_pair {} a b,s) \<Rightarrow> t \<Down> s' \<and> s' a = x \<and> s' b = y ))"
  sorry

definition encode_pair :: "_\<Rightarrow>_\<Rightarrow>_\<Rightarrow>_\<Rightarrow>com" where
  "encode_pair S a b c = undefined"

lemma encode_pair_correct:
  "finite S \<Longrightarrow> (\<forall>s. (\<exists>t s'. (encode_pair S a b c,s) \<Rightarrow> t \<Down> s' \<and> s' c = enc_pair (s a, s b) \<and> (\<forall>v\<in>S. s' v = s v)))"
  sorry


lemma finite_vars: "finite (vars f)"
  sorry

theorem (* Sanity check for definition of NP and poly-reduction *)
  assumes "D' \<in> NP"
    and "D \<le>\<^sub>I D'"
  shows
    "D \<in> NP"
proof -
  from assms(1) obtain P_D' p_c_D' p_t_D' where
      "poly p_t_D'" "poly p_c_D'" and
     *: "(\<And>x. x \<in> D'
                     \<longleftrightarrow> (\<exists>c. c \<le> p_c_D' x \<and> 
                            (\<forall>s. s ''x'' = enc_pair (x,c)
                                 \<longrightarrow> (\<exists>t s'. (P_D',s) \<Rightarrow> t \<Down> s' \<and> t \<le> p_t_D' x \<and> s' ''r'' = 1) 
                            )
                         )
                  )"
    unfolding NP_def sorry

  from assms(2) obtain f p_f where
    "poly p_f" and f:
    "(\<And>x s. s ''x'' = x \<Longrightarrow>
            (\<exists>t s'. (f,s) \<Rightarrow> t \<Down> s' \<and> t \<le> p_f (size(x)) \<and> (s' ''r'' \<in> D' \<longleftrightarrow> x \<in> D)))"
    unfolding IMP_reduction_alt
    by blast

  (* f's time and result only depends on ''x'' *)
  have "\<And>s1 s2 s1' s2' t1 t2. s1 ''x'' = s2 ''x'' \<Longrightarrow> (f,s1) \<Rightarrow> t1 \<Down> s1' \<Longrightarrow> (f,s2) \<Rightarrow> t2 \<Down> s2' \<Longrightarrow> t1=t2 \<and> s1' ''r'' = s2' ''r''" 
    sorry

  have "\<And>P Q. (~(\<forall>x. P x \<longrightarrow> Q x)) \<longleftrightarrow> (\<exists>x. P x \<and> ~ Q x)" by blast  

  (* get the variables that f writes *)
  (* get a variable that is not written by f *)
  from finite_vars[of f] obtain v where
      "v \<notin> vars f" 
    using ex_new_if_finite infinite_UNIV_listI by blast

  define P where "P = decode_pair {} ''x'' v ;; (
            f ;; (
            encode_pair {} ''r'' v ''x'';;
            P_D') )" (* P should expect input (x,c),
          first, decode (x,c) into x and c,
          write x into ''x'', and c into a fresh variable not written by f,
          execute f on x to obtain an input x' for D', 
          now encode (x',c) into ''x''
          then execute P_D' on on (x',c) to get the right result *) 

  show "D \<in> NP"
    unfolding NP_def
    apply safe
    apply(rule bexI[where x=P])
    apply(rule exI[where x=p_t_D'])
    apply(rule exI[where x=p_c_D'])
    apply safe
    subgoal sorry
    subgoal sorry
  proof -
    fix x
    assume a: "x\<in>D"
    (* we have the x:D, now "execute" f to get a x':D'*)
    from f[of "0(''x'':=x)" x] obtain t s'
      where "(f, 0(''x'' := x)) \<Rightarrow> t \<Down> s' \<and> t \<le> p_f (size x)" and 2: "(s' ''r'' \<in> D') = (x \<in> D)"
      by auto
    (* from that one get a witness c *)
    from a 2 *[of "s' ''r''"] obtain c where "c\<le>p_c_D' (s' ''r'')"
        and "\<And>s. s ''x'' = enc_pair (s' ''r'', c) \<Longrightarrow> (\<exists>t s'a. (P_D', s) \<Rightarrow> t \<Down> s'a \<and> t \<le> p_t_D' (s' ''r'') \<and> s'a ''r'' = 1)"
      by blast

    show "\<exists>c\<le>p_c_D' x. \<forall>s. s ''x'' = enc_pair (x, c) \<longrightarrow> (\<exists>t s'. (P, s) \<Rightarrow> t \<Down> s' \<and> t \<le> p_t_D' x \<and> s' ''r'' = 1)"
      (* now use the witness c *)
      apply(rule exI[where x=c])
      apply safe 
      subgoal        
        sorry
      unfolding P_def
      subgoal for s
      apply(drule decode_pair_correct'[where a="''x''" and b=v and s=s and x=x and y=c])
        apply safe
        apply rule
        apply rule
        apply safe
        apply(rule Seq) apply simp
           apply(rule Seq) 
             apply(drule f) apply safe
        sorry
      sorry
  next
    (* könnte funktionieren mit proof by contradiction *)

  qed

  oops


section \<open>Witness Existence\<close>

definition "WI = { enc_pair (enc_program P, enc_pair (x,T)) | P x T. \<exists>c. c\<le>T 
                                \<and> (\<forall>s. s ''x'' = enc_pair (x,c) \<longrightarrow> (\<exists>t s'. (P,s) \<Rightarrow> t \<Down> s'
                                                               \<and> t \<le> T \<and> s' ''r'' = 1 )) }"


lemma "NP_hard WI"
  unfolding NP_hard_def IMP_reduction_alt
proof 
  fix D'
  assume "D' \<in> NP"
  then obtain P_D' p_c_D' p_t_D' where
      "poly p_t_D'" "poly p_c_D'" and
     *: "(\<And>x. x \<in> D'
                     \<longleftrightarrow> (\<exists>c. c \<le> p_c_D' x \<and> 
                            (\<forall>s. s ''x'' = enc_pair (x,c)
                                 \<longrightarrow> (\<exists>t s'. (P_D',s) \<Rightarrow> t \<Down> s' \<and> t \<le> p_t_D' x \<and> s' ''r'' = 1) 
                            )
                         )
                  )"
    unfolding NP_def by blas

  define p_f where "p_f = (\<lambda>n::nat. n)"
  have "poly p_f" sorry
  define f where "f \<equiv> SKIP"
  (* f = do { ''r'' := enc_pair(enc_program P_D', ''x'' }  *)

  have "\<And>x. (\<And>s. s ''x'' = x \<Longrightarrow> (\<exists>t s'. (f,s) \<Rightarrow> t \<Down> s' \<and> t \<le> p_f x 
                                            \<and> s' ''r'' = enc_pair (enc_program P_D', x)))"
    sorry


  show "\<exists>p. poly p \<and>
              (\<exists>f. \<forall>x. (x \<in> D') =
                       (\<forall>s. s ''x'' = x \<longrightarrow> (\<exists>t s'. (f, s) \<Rightarrow> t \<Down> s' \<and> t \<le> p (size x) \<and> s' ''r'' \<in> WI)))"
    apply(rule exI[where x=p_f])
    apply safe
     apply fact
    apply(rule exI[where x=f])
    apply rule
    subgoal for x
      unfolding *[of x]
      apply safe
    proof -
      fix c s
      assume "c \<le> p_c_D' (s ''x'')"
      assume " \<forall>sa. sa ''x'' = enc_pair (s ''x'', c) \<longrightarrow>
                 (\<exists>t s'. (P_D', sa) \<Rightarrow> t \<Down> s' \<and> t \<le> p_t_D' (s ''x'') \<and> s' ''r'' = 1)"
      then have *: "\<And>sa. sa ''x'' = enc_pair (s ''x'', c) \<Longrightarrow>
                 (\<exists>t s'. (P_D', sa) \<Rightarrow> t \<Down> s' \<and> t \<le> p_t_D' (s ''x'') \<and> s' ''r'' = 1)"
        by blast
      assume "x = s ''x''"
      show "\<exists>t s'. (f, s) \<Rightarrow> t \<Down> s' \<and> t \<le> p_f (size (s ''x'')) \<and> s' ''r'' \<in> WI"
        

        
        
  


section \<open>Definition of SAT\<close>

text \<open>SAT is the set of all numbers that encode an satisfiable boolean formula.\<close>

definition "SAT = {n. \<exists>cnf. enc_formula(cnf) = n \<and> sat cnf}"


subsection \<open>Show that SAT is NP\<close>

text \<open>show that SAT is in NP by giving a IMP- program that certifies SAT by evaluating an 
    formula x for an assignment c.\<close>



section \<open>Translation Lemma\<close>

definition compile_to_SAT :: com where
  "compile_to_SAT = undefined"

lemma compile_to_SAT_refine:
  defines "p_to_sat_refine x \<equiv> x"
  assumes "s ''P'' = enc_program P"
      and "s ''x'' = x"
      and "s ''q'' = q"
    shows
  "\<exists>t s'. (toSAT, s) \<Rightarrow> t \<Down> s' \<and> t \<le> p_to_sat_refine (enc_program P + x + c + q)
      \<and> (\<exists>cnf. s' ''r'' = enc_formula cnf \<and> (sat cnf \<longleftrightarrow> ( result (P,x) = 1 \<and> time (P,x) \<le> q)))"
  sorry



section \<open>Statment of Cook-Levin Theorem\<close>


lemma result_fulfills:
  "(\<forall>s. s ''x'' = x \<longrightarrow> (\<exists>s' t . (p,s) \<Rightarrow> t \<Down> s' \<longrightarrow> P (s' ''r''))) \<Longrightarrow> P (result (p,x))"
  sorry

theorem cook_levin:
"\<forall>D\<in>NP.
  (\<exists>p. poly p \<and>
    (\<exists>f::com.
      (\<forall>x. time (f,x) \<le> p x
          \<and> (x \<in> D \<longleftrightarrow> (result (f,x)) \<in> SAT))))"
proof 
  fix D
  assume "D\<in>NP"
  then obtain P_D p_t_D p_c_D where
      "poly p_t_D" and "poly p_c_D" and
    *: "(\<forall>x. x \<in> D
                     \<longleftrightarrow> (\<exists>c. c \<le> p_c_D x \<and> 
                            (\<forall>s. s ''x'' = enc_pair(x,c)
                                 \<longrightarrow> (\<exists>t s'. (P_D,s) \<Rightarrow> t \<Down> s' \<and> t \<le> p_t_D x \<and> s' ''r'' = 1) 
                            )
                         )
                  )"
    unfolding NP_def by auto

  define p where "p = (\<lambda>n::nat. undefined::nat)" (* this polynomial bounds q (from P_D only run p_D steps ) *) 
  have poly_p: "poly p" sorry
  define f where "f = SKIP" (* this program should do the following:
        it expects the input on register ''x''
          do { ''P'' := enc_program(P_D); (1)
               ''q'' := poly_q(size(x));  (2)
               toSAT                      (3)
          }
      *)  


  show "(\<exists>p. poly p \<and>
    (\<exists>f::com.
      (\<forall>x. time (f,x) \<le> p x
          \<and> (x \<in> D \<longleftrightarrow> (result (f,x)) \<in> SAT))))"
    apply(rule exI[where x="p"])
    apply rule
     apply fact
    apply(rule exI[where x="f"])
  proof  safe
    fix x
    show "time (f, x) \<le> p x" 
      sorry
  next
    fix x
    assume "x \<in> D"
    with * obtain c where
      "c \<le> p_c_D x"
       "(\<forall>s. s ''x'' = enc_pair (x,c)
                                 \<longrightarrow> (\<exists>t s'. (P_D,s) \<Rightarrow> t \<Down> s' \<and> t \<le> p_t_D x \<and> s' ''r'' = 1) 
                            )"
      by meson

    (* TODO: f terminates *)
    (* (1) terminates *)
    (* (2) terminates *)
    (* (3) terminates with the correct result *)

    have f_simulates_p: "result (f,x) = result (P_D,enc_pair (x,c))"
      sorry

    have "(\<forall>s. s ''x'' = "

    thm compile_to_SAT_refine

    show "result (f,x) \<in> SAT"
      unfolding f_simulates_p
      apply(rule result_fulfills)



qed




section \<open>SAT is NP-complete\<close>


lemma "NP_complete SAT"
  sorry


end

end