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
print_theorems


lemma SeqD: "(c1;;c2,s) \<Rightarrow> t \<Down> s'' \<Longrightarrow> (\<exists>t1 t2 s'. (c1,s) \<Rightarrow> t1 \<Down> s' \<and> (c2,s') \<Rightarrow> t2 \<Down> s'' \<and> t = t1 + t2)"
  apply(cases rule: big_step_t.cases) apply simp
       apply simp_all
  apply auto done
  

lemma seq_post: "(\<exists>t1 s' t2 s''. (c1,s) \<Rightarrow> t1 \<Down> s' \<and> (c2,s') \<Rightarrow> t2 \<Down> s'' \<and> Q (t1+t2) s'') \<Longrightarrow> (\<exists>t s''. (c1;;c2,s) \<Rightarrow> t \<Down> s'' \<and> Q t s'')"
  apply auto
  subgoal for t1 s' t2 s''
    apply(rule exI[where x="t1+t2"])
    apply(rule exI[where x=s''])
    apply simp
    apply rule apply simp_all
    done
  done

fun vars :: "com \<Rightarrow> register set" where
  "vars SKIP = {}"
|  "vars (c1;;c2) = vars c1 \<union> vars c2"


lemma finite_vars: "finite (vars f)"
  sorry

lemma f_only_changes_its_vars: "v \<notin> vars f \<Longrightarrow> (f,s) \<Rightarrow> t \<Down> s' \<Longrightarrow> s' v = s v"
  sorry

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


lemma deterministic: "(c, s) \<Rightarrow> t1 \<Down> s1' \<Longrightarrow> (c, s) \<Rightarrow> t2 \<Down> s2' \<Longrightarrow> t1 = t2 \<and> s1' = s2'"
  sorry

definition depends_only_on_input where
  "depends_only_on_input P \<equiv> (\<forall>s1 s1' t s2. s1 ''x'' = s2 ''x'' \<longrightarrow> ((P,s1) \<Rightarrow> t \<Down> s1')
                                  \<longrightarrow> (\<exists>s2'. ((P,s2) \<Rightarrow> t \<Down> s2') \<and> s1' ''r'' = s2' ''r''))"


lemma depends_only_on_inputD:
  assumes  "depends_only_on_input c"
  shows "\<And>s1 s1' t1 t2 s2 s2'. s1 ''x'' = s2 ''x'' \<Longrightarrow> ((c,s1) \<Rightarrow> t1 \<Down> s1')
                      \<Longrightarrow> (\<exists>t2 s2'. ((c,s2) \<Rightarrow> t2 \<Down> s2') \<and> t1 = t2 \<and>  s1' ''r'' = s2' ''r'')"
  using assms unfolding depends_only_on_input_def 
  using deterministic  by blast

definition deterministic_on_input where
  "deterministic_on_input P \<equiv> (\<forall>s1 s2 s1' s2' t1 t2. s1 ''x'' = s2 ''x'' \<longrightarrow> (P,s1) \<Rightarrow> t1 \<Down> s1'
      \<longrightarrow>  (P,s2) \<Rightarrow> t2 \<Down> s2' \<longrightarrow> t1=t2 \<and> s1' ''r'' = s2' ''r'')"  


lemma deterministic_on_inputD:
  assumes  "deterministic_on_input c"
  shows "\<And>s1 s2 s1' s2' t1 t2. s1 ''x'' = s2 ''x'' \<Longrightarrow> (c,s1) \<Rightarrow> t1 \<Down> s1' \<Longrightarrow>  (c,s2) \<Rightarrow> t2 \<Down> s2' \<Longrightarrow> t1=t2 \<and> s1' ''r'' = s2' ''r''"
  using assms unfolding deterministic_on_input_def 
  by blast


lemma 
  deterministic_on_input_if_depends_only_on_input:
  assumes d:"depends_only_on_input P"
  shows "deterministic_on_input P"
  unfolding deterministic_on_input_def
proof (rule)+
  fix s1 s2 s1' s2' t1 t2
  assume x: "s1 ''x'' = s2 ''x''" and P: "(P, s1) \<Rightarrow> t1 \<Down> s1'" and Ps2a: "(P, s2) \<Rightarrow> t2 \<Down> s2'"
  
  from d[THEN depends_only_on_inputD, OF _ P, of s2, OF x] obtain t3 s3'
    where Ps2b: "(P, s2) \<Rightarrow> t3 \<Down> s3'" and 3: "t1 = t3" "s1' ''r'' = s3' ''r'' " by blast

  from deterministic[OF Ps2a Ps2b]
    have 2: "t2 = t3 \<and> s2' = s3'" by simp

  show "t1=t2" using 2 3 by simp
  show "s1' ''r'' = s2' ''r''" using 2 3 by simp
qed



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


section \<open>Axiomatize IMP- programs that decode and encode\<close>
(*
definition decode_pair' :: "_\<Rightarrow>_\<Rightarrow>_\<Rightarrow>com" where
  "decode_pair' S a b = undefined"

lemma decode_pair'_correct:
  "finite S \<Longrightarrow> (\<forall>s. s ''x'' = enc_pair (x, y) \<longrightarrow> 
    (\<exists>t s'. (decode_pair' S a b,s) \<Rightarrow> t \<Down> s' \<and> s' a = x \<and> s' b = y \<and> (\<forall>v\<in>S. s' v = s v)))"
  sorry *)

definition decode_pair :: "_\<Rightarrow>_\<Rightarrow>com" where
  "decode_pair  a b = undefined"


\<comment> \<open>The specification of decode_pair needs to have a polynomial running time bound\<close>
lemma decode_pair_correct':
  "(s ''x'' = enc_pair (x, y) \<Longrightarrow> 
    (\<exists>t s'. (decode_pair  a b,s) \<Rightarrow> t \<Down> s' \<and> s' a = x \<and> s' b = y ))"
  sorry

lemma decode_pair_deterministic:
  "s ''x'' = s2 ''x'' \<Longrightarrow> (decode_pair a b,s) \<Rightarrow> t \<Down> s' \<Longrightarrow> (decode_pair a b,s2) \<Rightarrow> t2 \<Down> s2'
    \<Longrightarrow> t=t2 \<and> s' a = s2' a \<and> s' b = s2' b"
  sorry

(*
definition encode_pair' :: "_\<Rightarrow>_\<Rightarrow>_\<Rightarrow>_\<Rightarrow>com" where
  "encode_pair' S a b c = undefined"

lemma encode_pair'_correct:
  "finite S \<Longrightarrow> (\<forall>s. (\<exists>t s'. (encode_pair' S a b c,s) \<Rightarrow> t \<Down> s' \<and> s' c = enc_pair (s a, s b) \<and> (\<forall>v\<in>S. s' v = s v)))"
  sorry
*)

definition encode_pair :: "_\<Rightarrow>_\<Rightarrow>_\<Rightarrow>com" where
  "encode_pair  a b c = undefined"


\<comment> \<open>The specification of encode_pair needs to have a polynomial running time bound\<close>

lemma encode_pair_correct:
  "(\<forall>s. (\<exists>t s'. (encode_pair a b c,s) \<Rightarrow> t \<Down> s' \<and> s' c = enc_pair (s a, s b)))"
  sorry

lemma encode_pair_determ:
  "s1 a = s2 a \<Longrightarrow> s1 b = s2 b \<Longrightarrow> (encode_pair a b c,s1) \<Rightarrow> t1 \<Down> s1' \<Longrightarrow> (encode_pair a b c,s2) \<Rightarrow> t2 \<Down> s2' \<Longrightarrow> 
      t1=t2 \<and> s1' c = s2' c"
  sorry



section \<open>P - deterministic polynomial computation\<close>


definition wf_com where
  "wf_com \<equiv> {P. depends_only_on_input P}"


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
                     \<longleftrightarrow> (\<exists>c. len c \<le> p_c (len x) \<and> 
                            (\<forall>s. s ''x'' = enc_pair (x,c)
                                 \<longrightarrow> (\<exists>t s'. (P,s) \<Rightarrow> t \<Down> s' \<and> t \<le> p_t (len (enc_pair (x,c))) \<and> s' ''r'' = 1) 
                            )
                         )
                  )
                )
        }"
  
(*  Attempt to define NP using the definition of P *)
lemma "D \<in> NP \<longleftrightarrow> (\<exists>D\<^sub>C\<in>P. (\<exists>p_c. poly p_c \<and> (\<forall>x. x\<in>D \<longleftrightarrow> (\<exists>c. len c \<le> p_c (len x) \<and> enc_pair(x,c) \<in> D\<^sub>C))))"
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
      subgoal premises p for s1 \<comment> \<open>The definition of @{term depends_only_on_input} does not necessarily need to ensure termination,
            here we already know that P terminates on s, and that it only depends on the value of ''x''.\<close>
        using p(1)[unfolded wf_com_def, simplified, THEN depends_only_on_inputD, of s s1, simplified p(6,10), OF _ p(7)]
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
            \<comment> \<open>The definition of @{term depends_only_on_input} does not necessarily need to ensure termination,
            here we already know that P terminates on s, and that it only depends on the value of ''x''.\<close>
          using prems(1)[unfolded wf_com_def, simplified, THEN depends_only_on_inputD, of s s1, simplified p(2,6), OF _ p(3)]
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
       (\<forall>x. time (f, x) \<le> p(len (x))
        \<and>  (x \<in> D \<longleftrightarrow> (result (f,x) ) \<in> D'))))"

text \<open>@{term \<open>A \<le>\<^sub>I B\<close>} : "A can be reduced to B".
    Intuition:
  \<^item> "B is at least as hard as A"
  \<^item> "if we can solve B, we can also solve A"
  \<^item> "if A is unsolvable, B also is"
   \<close>

text \<open>That's the definition I use later, is it equivalent to the above definition?\<close>
lemma IMP_reduction_alt:
  "D \<le>\<^sub>I D' =
   (\<exists>p_t p_r. poly p_t \<and> poly p_r \<and> 
     (\<exists>f\<in>wf_com.
       (\<forall>x. ((\<forall>s. s ''x'' = x \<longrightarrow> (\<exists>t s'. (f,s) \<Rightarrow> t \<Down> s' \<and> t \<le> p_t (len (x))
                               \<and> len (s' ''r'') \<le> p_r (len x) \<and> (s' ''r'' \<in> D' \<longleftrightarrow> x \<in> D)))))))"
  sorry
 
(* TODO: define NP hard *)

definition "NP_hard D = (\<forall>D'\<in>NP. D' \<le>\<^sub>I D)"

(* TODO: define NP-complete *)

text \<open>A problem in B in NP is NP-complete if, for any problem in NP, there is a polynomial-time reduction from A to B\<close>

definition "NP_complete D = undefined"

(*    assumes "D' \<in> NP"and "D \<le>\<^sub>I D'"shows "D \<in> NP" *)
theorem (* Sanity check for definition of NP and poly-reduction *)
  inNP_if_reducible_to_inNP:
  assumes "D' \<in> NP"
    and "D \<le>\<^sub>I D'"
  shows
    "D \<in> NP"
proof -
  from assms(1) obtain P_D' p_c_D' p_t_D' where
     wf_P_D': "P_D'\<in>wf_com" and "poly p_t_D'" "poly p_c_D'" and
     *: "(\<And>x. x \<in> D'
                     \<longleftrightarrow> (\<exists>c. len c \<le> p_c_D' (len x) \<and> 
                            (\<forall>s. s ''x'' = enc_pair (x,c)
                                 \<longrightarrow> (\<exists>t s'. (P_D',s) \<Rightarrow> t \<Down> s' \<and> t \<le> p_t_D' (len (enc_pair (x,c))) \<and> s' ''r'' = 1) 
                            )
                         )
                  )"
    unfolding NP_def by auto

  from assms(2) obtain f p_f p_r where
    "poly p_f" "poly p_r" and wf_f: "f\<in>wf_com" and f:
    "(\<And>x s. s ''x'' = x \<Longrightarrow>
            (\<exists>t s'. (f,s) \<Rightarrow> t \<Down> s' \<and> t \<le> p_f (len (x)) \<and> len (s' ''r'') \<le> p_r (len x) \<and> (s' ''r'' \<in> D' \<longleftrightarrow> x \<in> D)))"
    unfolding IMP_reduction_alt
    by blast

  have df: "depends_only_on_input f"
    using wf_f unfolding wf_com_def   by blast
  have dP_D': "depends_only_on_input P_D'"
    using wf_P_D' unfolding wf_com_def   by blast

  (* f's time and result only depends on ''x'' *)
  have f_dep: "\<And>s1 s2 s1' s2' t1 t2. s1 ''x'' = s2 ''x'' \<Longrightarrow> (f,s1) \<Rightarrow> t1 \<Down> s1' \<Longrightarrow> (\<exists>s2' t2.  (f,s2) \<Rightarrow> t2 \<Down> s2' \<and> t1=t2 \<and> s1' ''r'' = s2' ''r'')" 
    using df depends_only_on_input_def by blast

  have f_dep2: "\<And>s1 s2 s1' s2' t1 t2. s1 ''x'' = s2 ''x'' \<Longrightarrow> (f,s1) \<Rightarrow> t1 \<Down> s1' \<Longrightarrow>  (f,s2) \<Rightarrow> t2 \<Down> s2' \<Longrightarrow> t1=t2 \<and> s1' ''r'' = s2' ''r''"  
    using df[THEN deterministic_on_input_if_depends_only_on_input] unfolding deterministic_on_input_def by auto 

  have P_D'_dep: "\<And>s1 s2 s1' s2' t1 t2. s1 ''x'' = s2 ''x'' \<Longrightarrow> (P_D',s1) \<Rightarrow> t1 \<Down> s1' \<Longrightarrow> (\<exists>s2' t2.  (P_D',s2) \<Rightarrow> t2 \<Down> s2' \<and> t1=t2 \<and> s1' ''r'' = s2' ''r'')" 
    using wf_P_D' unfolding wf_com_def depends_only_on_input_def   by blast

  have P_D'_dep2: "\<And>s1 s2 s1' s2' t1 t2. s1 ''x'' = s2 ''x'' \<Longrightarrow> (P_D',s1) \<Rightarrow> t1 \<Down> s1' \<Longrightarrow>  (P_D',s2) \<Rightarrow> t2 \<Down> s2' \<Longrightarrow> t1=t2 \<and> s1' ''r'' = s2' ''r''" 
    using dP_D'[THEN deterministic_on_input_if_depends_only_on_input] unfolding deterministic_on_input_def by auto 


  have "\<And>P Q. (~(\<forall>x. P x \<longrightarrow> Q x)) \<longleftrightarrow> (\<exists>x. P x \<and> ~ Q x)" by blast  

  (* get the variables that f writes *)
  (* get a variable that is not written by f *)
  from finite_vars[of f] obtain v where
      vnf: "v \<notin> vars f" 
    using ex_new_if_finite infinite_UNIV_listI by blast

  thm f_only_changes_its_vars

  define P where "P = decode_pair ''x'' v ;; (
            f ;; (
            encode_pair ''r'' v ''x'';;
            P_D') )" (* P should expect input (x,c),
          first, decode (x,c) into x and c,
          write x into ''x'', and c into a fresh variable not written by f,
          execute f on x to obtain an input x' for D', 
          now encode (x',c) into ''x''
          then execute P_D' on on (x',c) to get the right result *) 

  have P_wf: "P \<in> wf_com" sorry \<comment> \<open>Prove that P is indeed wellformed, i.e. if it terminates, the result only depends on the input x.\<close>

  let ?pp = "(\<lambda>x. p_c_D' (p_r x))"

  
  have p_c_D'_mono: "\<And>x y. x\<le>y \<Longrightarrow> p_c_D' x \<le> p_c_D' y"  sorry \<comment> \<open>add monotonicity of the bounding polynomial to the definition of NP ?\<close>

  show "D \<in> NP"
    unfolding NP_def
    apply safe
    apply(rule bexI[where x=P])
     apply(rule exI[where x=ppp]) 
          \<comment> \<open>specify the running time bound.
              it should contain: 
                - decode_time
                - p_f
                - encode_time
                - p_t_D'
            \<close>
    apply(rule exI[where x="?pp"])
    apply safe
    subgoal sorry \<comment> \<open>Prove that the bound on the running time of P is poly\<close>
    subgoal sorry \<comment> \<open>Prove that the bound on the size the certificate is polynomial\<close>
  proof -
    fix x
    assume a: "x\<in>D"
    \<comment> \<open>we have the x:D, now "execute" f to get a x':D'\<close>
    from f[of "0(''x'':=x)" x] obtain t s'
      where f_0: "(f, 0(''x'' := x)) \<Rightarrow> t \<Down> s'" and lens'r: "len (s' ''r'') \<le> p_r (len x)"
          and "t \<le> p_f (len x)" and 2: "(s' ''r'' \<in> D') = (x \<in> D)"
      by auto
    \<comment> \<open>from that one get a witness c\<close>
    from a 2 *[of "s' ''r''"] obtain c where len_c: "len c\<le>p_c_D' (len (s' ''r''))"
        and co: "\<And>s. s ''x'' = enc_pair (s' ''r'', c) \<Longrightarrow> (\<exists>t s'a. (P_D', s) \<Rightarrow> t \<Down> s'a \<and> t \<le> p_t_D' (len (enc_pair (s' ''r'', c))) \<and> s'a ''r'' = 1)"
      by blast


    show "\<exists>c. len c\<le>?pp (len x) \<and> (\<forall>s. s ''x'' = enc_pair (x, c) \<longrightarrow> (\<exists>t s'. (P, s) \<Rightarrow> t \<Down> s' \<and> t \<le> ppp (len (enc_pair (x, c))) \<and> s' ''r'' = 1))"
      (* now use the witness c *)
      apply(rule exI[where x=c])
      apply safe 
      subgoal      
        apply(rule order.trans[OF len_c])
        apply(rule p_c_D'_mono)
        by(rule lens'r)
      unfolding P_def
      subgoal for s
        apply(rule seq_post)
      apply(drule decode_pair_correct'[where a="''x''" and b=v and s=s and x=x and y=c])
        apply safe
        subgoal for tt1 ss1
          apply(rule exI[where x=tt1])
          apply(rule exI[where x=ss1])
          apply simp
          apply(rule seq_post)
          subgoal premises p using f[of ss1 x, OF p(2)[symmetric]]
            apply rule apply clarsimp
            subgoal for tt2 ss2
              apply(rule exI[where x=tt2])
              apply(rule exI[where x=ss2])
              apply simp
              apply(rule seq_post)

              using encode_pair_correct[rule_format, of "''r''" v "''x''" ss2]
              apply clarsimp
              subgoal for tt3 ss3
                apply(rule exI[where x=tt3])
                apply(rule exI[where x=ss3])
                apply simp
                subgoal premises p2
                  using f_dep2[OF _ p2(1) f_0] p(2)[symmetric] apply simp 
                  using co[of ss3] using p2(6) p(3) f_only_changes_its_vars[OF vnf p2(1) ]
                  apply simp apply safe
                  subgoal for tt4 ss4
                    apply(rule exI[where x=tt4])
                    apply(rule exI[where x=ss4]) apply simp
                    subgoal sorry \<comment> \<open>Prove that the running time is indeed bounded by the bound stated.\<close>
                    done
                  done
                done
              done
            done
          done
        done
      done
  next
    fix x c
    assume lenc: "len c \<le> p_c_D' (p_r (len x))"
       and a: "\<forall>s. s ''x'' = enc_pair (x, c) \<longrightarrow> (\<exists>t s'. (P, s) \<Rightarrow> t \<Down> s' \<and> t \<le> ppp (len (enc_pair (x, c))) \<and> s' ''r'' = 1)"

    from a[rule_format, of "0(''x'':=enc_pair (x, c))"]
    obtain t4 s4 where P4: "(P, 0(''x'' := enc_pair (x, c))) \<Rightarrow> t4 \<Down> s4" and t4: "t4 \<le> ppp (len (enc_pair (x, c)))" and s4r: "s4 ''r'' = 1 "
      by auto

    from P4[unfolded P_def, THEN SeqD] obtain t1 tr1 s1 where
     d1: "(decode_pair ''x'' v, 0(''x'' := enc_pair (x, c))) \<Rightarrow> t1 \<Down> s1"
     and  r1: "(f;; (encode_pair ''r'' v ''x'';; P_D'), s1) \<Rightarrow> tr1 \<Down> s4" and "t4 = t1 + tr1 "
      by blast

    from  decode_pair_correct'[of "0(''x'' := enc_pair (x, c))" x c "''x''" v ]
    obtain t1' s1' where d2: "(decode_pair ''x'' v, 0(''x'' := enc_pair (x, c))) \<Rightarrow> t1' \<Down> s1'"
        and d2_corr: "s1' ''x'' = x" "s1' v = c" by auto

    term t1

    from  decode_pair_deterministic[OF _ d1 d2]
    have 11: "t1 = t1' \<and> s1 ''x'' = s1' ''x'' \<and> s1 v = s1' v"  by auto

    have s1v: "s1 v = c" using d2_corr 11 by simp

    from f[of s1 x] obtain t2' s2'
      where f_0: "(f, s1) \<Rightarrow> t2' \<Down> s2'" and lens'r: "len (s2' ''r'') \<le> p_r (len x)"
          and "t2' \<le> p_f (len x)" and 2: "(s2' ''r'' \<in> D') = (x \<in> D)"
      using d2_corr 11
      by auto

    from r1[THEN SeqD] obtain t2 tr2 s2 where
      f1:  "(f, s1) \<Rightarrow> t2 \<Down> s2" and r2: "(encode_pair ''r'' v ''x'';; P_D', s2) \<Rightarrow> tr2 \<Down> s4" and "tr1 = t2 + tr2"
      by blast

    from f_dep2[OF _ f_0 f1] have 22: "t2' = t2" "s2' ''r'' = s2 ''r''" by auto

    from r2[THEN SeqD] obtain t3 tr3 s3 where
      e1:  "(encode_pair ''r'' v ''x'', s2) \<Rightarrow> t3 \<Down> s3" and r3: "(P_D', s3) \<Rightarrow> tr3 \<Down> s4" and "tr2 = t3 + tr3"
      by blast

    from f_only_changes_its_vars[OF vnf  f1] have s2v: "s2 v = s1 v" by simp

    from  encode_pair_correct[rule_format, of "''r''" v "''x''" s2] 
    obtain t3' s3' where e2: "(encode_pair ''r'' v ''x'', s2) \<Rightarrow> t3' \<Down> s3'"
        and e3_corr: "s3' ''x'' = enc_pair (s2 ''r'', s2 v)" by auto

    from encode_pair_determ[OF _ _ e1 e2] have 3: "t3 = t3' \<and> s3 ''x'' = s3' ''x''"
      by auto

    define x' where "x' = s2 ''r''"
    have "(\<exists>c. len c \<le> p_c_D' (len x') \<and> (\<forall>s. s ''x'' = enc_pair (x', c) \<longrightarrow> (\<exists>t s'. (P_D', s) \<Rightarrow> t \<Down> s' \<and> t \<le> p_t_D' (len (enc_pair (x', c))) \<and> s' ''r'' = 1)))"
      apply(rule exI[where x=c])
      apply safe
      subgoal
        unfolding x'_def
        apply(rule order.trans) 
         apply(rule lenc)   
        apply(rule p_c_D'_mono)
        using lens'r sorry \<comment> \<open>Whoopsie, why is that?\<close>
    proof (goal_cases)
      case g: (1 ss) 
      from P_D'_dep[OF _ r3, of ss] e3_corr[folded x'_def, unfolded s2v s1v] 3 g
      obtain ss2' tt2 where ta: "(P_D', ss) \<Rightarrow> tt2 \<Down> ss2'" and "tr3 = tt2" and ta3: "s4 ''r'' = ss2' ''r''" by auto


      from P_D'_dep2[OF _ ta r3] e3_corr[folded x'_def, unfolded s2v s1v] 3 g
        have 44: "tt2 = tr3 \<and> ss2' ''r'' = s4 ''r''" by auto
                 
      show ?case apply(rule exI[where x=tt2]) 
        apply(rule exI[where x=ss2'])
        apply safe
        subgoal using ta by simp
        subgoal using t4  sorry \<comment> \<open>the running time bound is a sum, it needs to be separated to get that estimation\<close>
        subgoal using ta3 s4r by simp
        done
    qed

    with * have "x'\<in>D'" by auto
    with x'_def 2 22 show "x\<in>D" by auto
  next
    show "P \<in> wf_com" by(fact P_wf)
  qed
qed


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