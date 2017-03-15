theory LL
imports Main "~~/src/HOL/Library/FSet" "~~/src/HOL/Library/Multiset" "~~/src/HOL/Library/Map" 
begin

datatype atm = atm string "nat list"
  
datatype form = 
  tru
  | fal
  | why form
  | amp form form 
  | par form form
  | imp form form 
  | lol form form
  | fatm atm
    
datatype seq =
  useq "form fset" "form multiset" "atm multiset" "form multiset" "form fset"
  | fseq "form fset" "form multiset" form "atm multiset" "form fset"

inductive derv :: "nat \<Rightarrow> seq \<Rightarrow> bool" where 
  rtru : "derv N (useq P D A (G + {#tru#}) Y)"
  | rfal : "derv N (useq P D A G Y) \<Longrightarrow> derv (N + 1) (useq P D A (G + {#fal#}) Y)"
  | fatm : "derv N (useq P D (A + {#X#}) G Y) \<Longrightarrow> derv (N + 1) (useq P D A (G + {#fatm X#}) Y)"
  | rwhy : "derv N (useq P D A G (Y |\<union>| {|F|})) \<Longrightarrow> derv (N + 1) (useq P D A (G + {#why F#}) Y)"
  | ramp : "derv N (useq P D A (G + {#B#}) Y) \<Longrightarrow> derv M (useq P D A (G + {#C#}) Y) \<Longrightarrow> derv ((max N M) + 1) (useq P D A (G + {#amp B C#}) Y)"
  | rpar : "derv N (useq P D A (G + {#B,C#}) Y) \<Longrightarrow> derv (N+1) (useq P D A (G + {#par B C#}) Y)"
  | rimp : "derv N (useq (P |\<union>| {|B|}) D A (G + {#C#}) Y) \<Longrightarrow> derv (N + 1) (useq P D A (G + {#imp B C#}) Y)"
  | rlol : "derv N (useq P (D + {#B#}) A (G + {#C#}) Y) \<Longrightarrow> derv (N + 1) (useq P D A (G + {#lol B C#}) Y)"
  | bangdecide : "F |\<in>| P \<Longrightarrow> derv N (fseq P D F A Y) \<Longrightarrow> derv (N + 1) (useq P D A {#} Y)" 
  | decide :  "derv N (fseq P D F A Y) \<Longrightarrow> derv (N + 1) (useq P (D + {#F#}) A {#} Y)"
  | whydecide : "F |\<in>| Y \<Longrightarrow> derv N (useq P D A {#F#} Y) \<Longrightarrow> derv (N + 1) (useq P D A {#} Y)"
  | lfal : "derv N (fseq G {#} fal {#} Y)"
  | lfatm : "derv N (fseq G {#} (fatm A) {#A#} Y)"
  | lwhy : "derv N (useq G {#F#} {#} {#} Y)  \<Longrightarrow> derv (N + 1) (fseq G {#} (why F) {#} Y)"
  | lamp1 : "derv N (fseq G D B A Y) \<Longrightarrow> derv (N + 1) (fseq G D (amp B C) A Y)"
  | lamp2 : "derv N (fseq G D C A Y) \<Longrightarrow> derv (N + 1) (fseq G D (amp B C) A Y)"
  | lpar : "derv  N (fseq G D1 B A1 Y) \<Longrightarrow> derv M (fseq G D2 C A2 Y) \<Longrightarrow> derv ((max N M) + 1) (fseq G (D1 + D2) (par B C) (A1 + A2) Y)"
  | limp : "derv  N (useq G {#} {#} {#B#} Y) \<Longrightarrow> derv M (fseq G D C A Y) \<Longrightarrow> derv ((max N M) + 1) (fseq G D (imp B C) A Y)"
  | llol : "derv  N (useq G D1 A1 {#B#} Y) \<Longrightarrow> derv M (fseq G D2 C A2 Y) \<Longrightarrow> derv ((max N M) + 1) (fseq G (D1 + D2) (lol B C) (A1 + A2) Y)"

fun h and g where
  "h fal = fal"
| "h tru = tru"
| "h (fatm A) = (fatm A)"
| "h (why F) = why (h F)"
| "h (amp B C) = amp (h B) (h C)"
| "h (par B C) =
  (case (h B, h C) of 
  (amp B1 B2, amp C1 C2) \<Rightarrow> (amp (amp (par B1 C1) (par B1 C2)) (amp (par B2 C1) (par B2 C2)))
  |(amp B1 B2, C') \<Rightarrow> (amp (par B1 C') (par B2 C'))
  |(B', amp C1 C2) \<Rightarrow> (amp (par B' C1) (par B' C2))
  |(B',C') \<Rightarrow> par B' C')"
| "h (imp B C) =
  (case (g B, h C) of 
  (B, amp C1 C2) \<Rightarrow> (amp (imp B C1) (imp B C2))
  |(B,C) \<Rightarrow> lol B C)"
| "h (lol B C) =
  (case (g B, h C) of 
  (B, amp C1 C2) \<Rightarrow> (amp (lol B C1) (lol B C2))
  |(B,C) \<Rightarrow> lol B C)"
| "g fal = fal"
| "g tru = tru"
| "g (fatm A) = (fatm A)"
| "g (why F) = why (g F)"
| "g (amp B C) = amp (g B) (g C)"
| "g (par B C) = par (g B) (g C)"
| "g (imp B C) = imp (h B) (g C)"
| "g (lol B C) = lol (h B) (g C)"

fun notamp where
  "notamp (amp A B) = False"
|"notamp _ = True"
  

theorem mset_union_mem: 
  "G = G1 + G2 \<Longrightarrow> (\<forall> x\<in>#G1. x\<in>#G) \<and> (\<forall> x\<in>#G2. x\<in>#G)" by auto

theorem mset_mem_union:
  "F \<in># G1 \<Longrightarrow> G = G1 + G2 \<Longrightarrow> F \<in># G" by auto
    
theorem mset_mem_split:
  "F \<in># G \<Longrightarrow> \<exists> G'. G = G' + {#F#}" using multi_member_split by fastforce

theorem mset_quarter_compose:
  "C1 + C2 = D1 + D2 \<Longrightarrow> \<exists> C11 C12 C21 C22. C1 = C11 + C12 \<and> C2 = C21 + C22 \<and> D1 = C11 + C21 \<and> D2 = C12 + C22"
  sorry

theorem lamp_destruct: "derv M (fseq P D (amp B C) A Y) \<Longrightarrow> (derv (M-1) (fseq P D B A Y) \<or> derv (M-1) (fseq P D C A Y))"
  apply(cases  rule: derv.cases)
                     apply auto
  done

theorem lpar_assoc: "derv M S \<Longrightarrow> S = (fseq P D (par B C) A Y) \<Longrightarrow> derv M (fseq P D (par C B) A Y)"
  apply(induct rule: derv.induct)
                    apply auto
    by (metis Suc_eq_plus1 lpar max.commute union_commute)

theorem lamp_assoc: "derv M S \<Longrightarrow> S = (fseq P D (amp B C) A Y) \<Longrightarrow> derv M (fseq P D (amp C B) A Y)"
  apply(induct rule: derv.induct)
                    apply auto
  using lamp2 apply auto[1]
  using lamp1 by auto

theorem lpar_lamp1_distrib: "derv M S \<Longrightarrow> S = (fseq P D (par (amp B1 B2) C) A Y) \<Longrightarrow> \<exists> M. derv M (fseq P D (amp (par B1 C) (par B2 C)) A Y)"
  apply(induct  rule: derv.cases)
                    apply(auto)
  by (meson lamp1 lamp2 lamp_destruct lpar) 
    
theorem lpar_lamp2_distrib: "derv M S \<Longrightarrow> S = (fseq P D (par B (amp C1 C2)) A Y) \<Longrightarrow> \<exists> M. derv M (fseq P D (amp (par B C1) (par B C2)) A Y)"
  by (metis lamp1 lamp2 lamp_destruct lpar_assoc lpar_lamp1_distrib)

theorem lpar_lamp12_distrib: "derv M S \<Longrightarrow> S = (fseq P D (par (amp B1 B2) (amp C1 C2)) A Y) 
\<Longrightarrow> \<exists> M. derv M (fseq P D (amp (amp (par B1 C1) (par B1 C2))  (amp (par B2 C1) (par B2 C2))) A Y)"
    apply(induct  rule: derv.cases)
                    apply(auto)
  proof -
    fix N :: nat and D1 :: "form multiset" and A1 :: "atm multiset" and Ma :: nat and D2 :: "form multiset" and A2 :: "atm multiset"
    assume a1: "derv N (fseq P D1 (amp B1 B2) A1 Y)"
  assume a2: "derv Ma (fseq P D2 (amp C1 C2) A2 Y)"
  assume "D = D1 + D2"
  assume "A = A1 + A2"
  have f3: "derv (Ma - 1) (fseq P D2 C2 A2 Y) \<or> derv (Ma - 1) (fseq P D2 C1 A2 Y)"
    using a2 lamp_destruct by blast
  have "derv (N - 1) (fseq P D1 B2 A1 Y) \<or> derv (N - 1) (fseq P D1 B1 A1 Y)"
    using a1 lamp_destruct by blast
  then show "\<exists>n. derv n (fseq P (D1 + D2) (amp (amp (par B1 C1) (par B1 C2)) (amp (par B2 C1) (par B2 C2))) (A1 + A2) Y)"
    using f3 by (meson lamp1 lamp2 lpar)
qed

lemma h_par_notamp2:" notamp(h C) \<Longrightarrow> h B = amp B1 B2  \<Longrightarrow> h(par B C) = (amp (par B1 (h C)) (par B2 (h C)))"  
  apply(induct "h C")
         apply auto
       apply (metis form.simps(65))
      apply (metis notamp.simps(1))
      apply (metis (no_types, lifting) form.simps(67))
    apply (metis (no_types, lifting) form.simps(68))
           apply (metis (no_types, lifting) form.simps(69))
  by (metis form.simps(70))
    
lemma h_par_notamp1:" notamp(h B) \<Longrightarrow> h C = amp C1 C2  \<Longrightarrow> h(par B C) = (amp (par (h B) C1) (par (h B) C2))" 
    apply(induct "h B")
         apply auto
       apply (metis (no_types, lifting) form.simps(65) form.simps(66))
      apply (metis notamp.simps(1))
 apply (smt form.simps(66) form.simps(67))
  apply (smt form.simps(66) form.simps(68))  
                apply (smt form.simps(66) form.simps(69))
  by (metis (mono_tags, lifting) form.simps(66) form.simps(70))

lemma h_par_notamp12:" notamp(h B) \<Longrightarrow> notamp(h C)  \<Longrightarrow> h(par B C) = par (h B) (h C)" 
  sorry
    
theorem a: 
"(derv N S' \<Longrightarrow>
 S' = (useq P' D' A G' Y') \<Longrightarrow>
 P' = P1|\<union>|P2 \<Longrightarrow>
 D' = D1+D2 \<Longrightarrow>
 G' = G1+G2 \<Longrightarrow>
 Y' = Y1|\<union>|Y2 \<Longrightarrow>
 P = P1|\<union>|(fimage h P2) \<Longrightarrow>
 D = D1+(image_mset h D2) \<Longrightarrow>
 G = G1+(image_mset g G2) \<Longrightarrow>
 Y =  Y1|\<union>|(fimage g Y2) \<Longrightarrow>
 \<exists> M. derv M (useq P D A G Y))"
"(derv N S' \<Longrightarrow>
 S' = (fseq P' D' F A Y') \<Longrightarrow>
 P' = P1|\<union>|P2 \<Longrightarrow>
 D' = D1+D2 \<Longrightarrow>
 Y' = Y1|\<union>|Y2 \<Longrightarrow>
 P = P1|\<union>|(fimage h P2) \<Longrightarrow>
 D = D1+(image_mset h D2) \<Longrightarrow>
 Y =  Y1|\<union>|(fimage g Y2) \<Longrightarrow>
 \<exists> M. derv M (fseq P D F A Y))"
"(derv N S' \<Longrightarrow>
 S' = (fseq P' D' F A Y') \<Longrightarrow>
 P' = P1|\<union>|P2 \<Longrightarrow>
 D' = D1+D2 \<Longrightarrow>
 Y' = Y1|\<union>|Y2 \<Longrightarrow>
 P = P1|\<union>|(fimage h P2) \<Longrightarrow>
 D = D1+(image_mset h D2) \<Longrightarrow>
 Y =  Y1|\<union>|(fimage g Y2) \<Longrightarrow>
 \<exists> M. derv M (fseq P D (h F) A Y))"
proof(induct arbitrary: P' P1 P2 D' D1 D2 G' G1 G2 Y' Y1 Y2 P D A G Y F rule: derv.inducts)
  case (rtru)
  case (1)
    then have "tru \<in># G1 \<or> tru \<in># G2" by (metis LL.seq.inject(1) add.commute multi_member_this union_iff)
    thus ?case
    proof
      assume H:"tru \<in># G1"
      then have H:"tru \<in># G" by (simp add: "1.prems"(8))
      then obtain Gpart where "Gpart + {#tru#} = G" using mset_mem_split[OF H] by auto
      thus ?case using derv.rtru by auto
    next
      assume H:"tru \<in># G2"
      then have H:"tru \<in># G" by (metis "1.prems"(8) g.simps(2) image_mset_add_mset insert_DiffM mset_union_mem union_single_eq_member)
      then obtain Gpart where "Gpart + {#tru#} = G" using mset_mem_split[OF H] by auto
      thus ?thesis using derv.rtru by auto  
    qed
next 
  case (rtru)
  case (2)
  show ?case sorry 
next 
  case (rtru)
  case (3)
  show ?case sorry 
next
    case (rfal _ P'' D'' A'' G'' Y'')
    case (1)
    then have "fal \<in># G1 \<or> fal \<in># G2" by (metis LL.seq.inject(1) add.commute multi_member_this union_iff)
    thus ?case
    proof
      assume H1:"fal \<in># G1"
      then have H2:"useq P'' D'' A'' G'' Y'' = useq P' D' A (G' - {#fal#}) Y'" using "1.prems"(1) by auto
      then have H3:"G' - {#fal#} = (G1 - {#fal#}) + G2" by (simp add: "1.prems"(4) H1)
      then have H4:"G - {#fal#} = G1 - {#fal#} + image_mset g G2" using "1.prems"(8) H1 by auto
      then obtain M where H5:"derv M (useq P D A (G - {#fal#}) Y)" 
      using "1.prems" rfal(2)[OF H2 "1.prems"(2) "1.prems"(3) H3 "1.prems"(5) "1.prems"(6) "1.prems"(7) H4 "1.prems"(9)] by auto
      thus ?case using derv.rfal[OF H5] using H1 "1.prems"(8) by auto 
    next
      assume H1:"fal \<in># G2"
      then have H2:"useq P'' D'' A'' G'' Y'' = useq P' D' A (G' - {#fal#}) Y'" using "1.prems"(1) by auto
      then have H3:"G' - {#fal#} = G1 + (G2 - {#fal#})" by (simp add: "1.prems"(4) H1)
      then have H4:"G - {#fal#} = G1 + (image_mset g (G2 - {#fal#}))"
      proof -
        have "image_mset g G2 - {#fal#} = image_mset g (G2 - {#fal#})"
          by (simp add: H1 image_mset_Diff)
        then show ?thesis
          by (metis (no_types) "1.prems"(8) H1 add_mset_remove_trivial_eq diff_union_single_conv g.simps(1) image_mset_add_mset)
      qed
      then obtain M where H5:"derv M (useq P D A (G - {#fal#}) Y)" 
        using "1.prems" rfal(2)[OF H2 "1.prems"(2) "1.prems"(3) H3 "1.prems"(5) "1.prems"(6) "1.prems"(7) H4 "1.prems"(9)] by auto
      thus ?case using derv.rfal[OF H5] by (metis add.right_neutral add_mset_remove_trivial_eq diff_single_trivial union_mset_add_mset_right) 
    qed
next 
  case (rfal)
  case (2)
  show ?case sorry 
next 
  case (rfal)
  case (3)
  show ?case sorry       
next
  case (fatm N P D A X G Y)
  case (1)
  then show ?case sorry
next
  case (fatm N P D A X G Y)
  case (2)
  then show ?case sorry
next
  case (fatm N P D A X G Y)
  case (3)
  then show ?case sorry      
next
  case (rwhy N P D A G Y F)
  case (1)
  then show ?case sorry
next
  case (rwhy N P D A G Y F)
  case (2)
  then show ?case sorry
next
  case (rwhy N P D A G Y F)
  case (3)
  then show ?case sorry      
next
  case (ramp N P D A G B Y M C)
  case (1)
  then show ?case sorry      
next
  case (ramp N P D A G B Y M C)
  case (2)
  then show ?case sorry      
next
  case (ramp N P D A G B Y M C)
  case (3)
  then show ?case sorry      
next
  case (rpar N P D A G B C Y)
  case (1)
  then show ?case sorry      
next
  case (rpar N P D A G B C Y)
  case (2)
  then show ?case sorry      
next
  case (rpar N P D A G B C Y)
  case (3)
  then show ?case sorry      
next
  case (rimp N P B D A G C Y)
  case (1)
  then show ?case sorry
next
  case (rimp N P B D A G C Y)
  case (2)
  then show ?case sorry
next
  case (rimp N P B D A G C Y)
  case (3)
  then show ?case sorry      
next
  case (rlol N P D B A G C Y)
  case (1)
  then show ?case sorry
next
  case (rlol N P D B A G C Y)
  case (2)
  then show ?case sorry
next
  case (rlol N P D B A G C Y)
  case (3)
  then show ?case sorry
next
    case (bangdecide F P'' N D'' A'' Y'')
    case (1)
    then have H1:"fseq P'' D'' F A'' Y'' = fseq P' D' F A Y'" by auto
    then have H2:"G = {#}" using "1.prems"(1) "1.prems"(4) "1.prems"(8) by auto
    then have "F |\<in>| P1 \<or> F |\<in>| P2" using "1.prems" bangdecide.hyps(1) by blast
    thus ?case
    proof
      assume A:"F |\<in>| P1"
      then obtain M where H3:"derv M (fseq P D F A Y)" 
        using bangdecide(4)[OF H1 "1.prems"(2) "1.prems"(3) "1.prems"(5) "1.prems"(6) "1.prems"(7) "1.prems"(9)] by auto
      then have H4:"F |\<in>| P" using A "1.prems"(6) by blast
      thus ?case using derv.bangdecide[OF H4 H3] H2 by auto
    next
      assume A:"F |\<in>| P2"
      then obtain M where H3:"derv M (fseq P D (h F) A Y)" 
        using bangdecide(5)[OF H1 "1.prems"(2) "1.prems"(3) "1.prems"(5) "1.prems"(6) "1.prems"(7) "1.prems"(9)] by auto
      then have H4:"h F |\<in>| P" using A "1.prems"(6) by blast
      thus ?case using derv.bangdecide[OF H4 H3] H2 by auto
    qed
next
  case (bangdecide F P'' N D'' A'' Y'')
  case (2)
  then show ?case sorry
next
  case (bangdecide F P'' N D'' A'' Y'')
  case (3)
  then show ?case sorry
next
  case (decide N P D F A Y)
  case (1)
  then show ?case sorry
next
  case (decide N P D F A Y)
  case (2)
  then show ?case sorry
next
  case (decide N P D F A Y)
  case (3)
  then show ?case sorry
next
  case (whydecide F Y N P D A)
  case (1)
  then show ?case sorry
next
  case (whydecide F Y N P D A)
  case (2)
  then show ?case sorry
next
  case (whydecide F Y N P D A)
  case (3)
  then show ?case sorry
next
  case (lfal N G Y)
  case (1)
  then show ?case sorry
next
  case (lfal N G Y)
  case (2)
  then show ?case sorry
next
  case (lfal N G Y)
  case (3)
  then show ?case sorry
next
  case (lfatm N G A Y)
  case (1)
  then show ?case sorry
next
  case (lfatm N G A Y)
  case (2)
  then show ?case sorry
next
  case (lfatm N G A Y)
  case (3)
  then show ?case sorry
next
  case (lwhy N G F Y)
  case (1)
  then show ?case sorry
next
  case (lwhy N G F Y)
  case (2)
  then show ?case sorry
next
  case (lwhy N G F Y)
  case (3)
  then show ?case sorry
next
  case (lamp1 N G D B A Y C)
  case (1)
  then show ?case sorry
next
  case (lamp1 N G D B A Y C)
  case (2)
  then show ?case sorry
next
  case (lamp1 N G D B A Y C)
  case (3)
  then show ?case sorry      
next
  case (lamp2 N G D C A Y B)
  case (1)
  then show ?case sorry
next
  case (lamp2 N G D C A Y B)
  case (2)
  then show ?case sorry
next
  case (lamp2 N G D C A Y B)
  case (3)
  then show ?case sorry      
next
  case (lpar N G D1 B A1 Y M D2 C A2)
      case (lpar N1 P'' D1'' B A1 Y'' N2 D2'' C A2)
    case (1)
    then have False using "1.prems"(1) by auto
    thus ?case by auto
  next
    case (lpar N1 P'' D1'' B A1 Y'' N2 D2'' C A2)
    case (2)
    then have H1:"D1 + D2 = D1'' + D2''" by auto
    then obtain D11 D12 D21 D22 where H21:"D1 = D11 + D12" and H22:"D2 = D21 + D22" and H23:"D1'' = D11 + D21" and H24:"D2'' = D12 + D22" using mset_quarter_compose[OF H1] by auto
    then obtain D1''h where H3:"D1''h = D11 + image_mset h D21" by auto
    then obtain M1 where H4:"derv M1  (fseq P D1''h B A1 Y)" using lpar(3)[OF _ "2.prems"(2) H23 "2.prems"(4) "2.prems"(5) H3 "2.prems"(7)] "2.prems"(1) by blast
    then obtain D2''h where H5:"D2''h = D12 + image_mset h D22" by auto
    then obtain M2 where H6:"derv M2  (fseq P D2''h C A2 Y)" using lpar(7)[OF _ "2.prems"(2) H24 "2.prems"(4) "2.prems"(5) H5 "2.prems"(7)] "2.prems"(1) by blast
    then have H7:"derv ((max M1 M2) + 1) (fseq P (D1''h + D2''h) (par B C) (A1 + A2) Y)" using derv.lpar[OF H4 H6] by auto
    then have "D = D1''h + D2''h" using H3 H5 H21 H22 by (simp add: "2.prems"(6))
    thus ?case using derv.rpar using "2"(1) H7 by blast     
  next
    case (lpar N1 P'' D1'' B A1 Y'' N2 D2'' C A2)
    case (3)
    then have H1:"D1 + D2 = D1'' + D2''" by auto
    then obtain D11 D12 D21 D22 where H21:"D1 = D11 + D12" and H22:"D2 = D21 + D22" and H23:"D1'' = D11 + D21" and H24:"D2'' = D12 + D22" using mset_quarter_compose[OF H1] by auto
    then obtain D1''h where H3:"D1''h = D11 + image_mset h D21" by auto
    then obtain M1 where H4:"derv M1  (fseq P D1''h (h B) A1 Y)" using lpar(4)[OF _ "3.prems"(2) H23 "3.prems"(4) "3.prems"(5) H3 "3.prems"(7)] "3.prems"(1) by blast
    then obtain D2''h where H5:"D2''h = D12 + image_mset h D22" by auto
    then obtain M2 where H6:"derv M2  (fseq P D2''h (h C) A2 Y)" using lpar(8)[OF _ "3.prems"(2) H24 "3.prems"(4) "3.prems"(5) H5 "3.prems"(7)] "3.prems"(1) by blast
    then have H7:"D = D1''h + D2''h" using H3 H5 H21 H22 by (simp add: "3.prems"(6))
    then have H8:"(\<exists> B1 B2 C1 C2. h B = amp B1 B2 \<and> h C = amp C1 C2) \<or>
                  ((\<exists> B1 B2. h B = amp B1 B2) \<and> notamp (h C)) \<or>
                  (notamp (h B) \<and> (\<exists> C1 C2. h C = amp C1 C2)) \<or>
                  (notamp (h B) \<and> notamp (h C))" by (meson notamp.elims(3))
    thus ?case
    proof 
      assume "(\<exists> B1 B2 C1 C2. h B = amp B1 B2 \<and> h C = amp C1 C2)"
      then obtain B1 B2 C1 C2 where H1:"h B = amp B1 B2" and H2:"h C = amp C1 C2" by auto
      then have H9:"h (par B C) = amp (amp (par B1 C1) (par B1 C2)) (amp (par B2 C1) (par B2 C2))" by auto
      then have H10:"derv ((max M1 M2) + 1) (fseq P (D1''h + D2''h) (par (amp B1 B2) (amp C1 C2)) (A1 + A2) Y)" using derv.lpar[OF H4 H6]
          by (simp add: H1 H2)  
      thus ?case using lpar_lamp12_distrib[OF H10] using "3.prems"(1) H7 H9 by auto
    next
      assume "((\<exists> B1 B2. h B = amp B1 B2) \<and> notamp (h C)) \<or>
                  (notamp (h B) \<and> (\<exists> C1 C2. h C = amp C1 C2)) \<or>
                  (notamp (h B) \<and> notamp (h C))"
      thus ?case
      proof
        assume A:"((\<exists>B1 B2. h B = amp B1 B2) \<and> notamp(h C))"
        then obtain B1 B2 where H1:"h B = amp B1 B2" by auto
        then have H9:"h (par B C) = amp (par B1 (h C)) (par B2 (h C))" using A h_par_notamp2 by blast
        then have H10:"derv ((max M1 M2) + 1) (fseq P (D1''h + D2''h) (par (amp B1 B2) (h C)) (A1 + A2) Y)" using derv.lpar[OF H4 H6] H1 by auto
        thus ?case using lpar_lamp1_distrib[OF H10] using "3.prems"(1) H7 H9 by auto
      next
        assume "(notamp (h B) \<and> (\<exists> C1 C2. h C = amp C1 C2)) \<or>
                  (notamp (h B) \<and> notamp (h C))"
        thus ?case
        proof
          assume A:"(notamp(h B) \<and> (\<exists>C1 C2. h C = amp C1 C2))"
          then obtain C1 C2 where H1:"h C = amp C1 C2" by auto
          then have H9:"h (par B C) = amp (par (h B) C1) (par (h B)  C2)" using A h_par_notamp1 by blast
          then have H10:"derv ((max M1 M2) + 1) (fseq P (D1''h + D2''h) (par (h B) (amp C1 C2)) (A1 + A2) Y)" using derv.lpar[OF H4 H6] H1 by auto
          thus ?case using lpar_lamp2_distrib[OF H10] using "3.prems"(1) H7 H9 by auto
        next
          assume A:"notamp (h B) \<and> notamp (h C)"
          then have H9:"h (par B C) = par (h B) (h C)"  using h_par_notamp12 by blast
          then have H10:"derv ((max M1 M2) + 1) (fseq P (D1''h + D2''h) (par (h B) (h C)) (A1 + A2) Y)" using derv.lpar[OF H4 H6] H1 by auto          
          then have H10:"derv ((max M1 M2) + 1) (fseq P (D1''h + D2''h) (h (par B C)) (A1 + A2) Y)" using H9 by auto
          thus ?case using H7 "3.prems"(1) H9 by blast
        qed
      qed
    qed
next
  case (limp N G B Y M D C A)
  case (1)
  then show ?case sorry
next
  case (limp N G B Y M D C A)
  case (2)
  then show ?case sorry
next
  case (limp N G B Y M D C A)
  case (3)
  then show ?case sorry
next
  case (llol N G D1 A1 B Y M D2 C A2)
  case (1)
  then show ?case sorry
next
  case (llol N G D1 A1 B Y M D2 C A2)
  case (2)
  then show ?case sorry
next
  case (llol N G D1 A1 B Y M D2 C A2)
  case (3)
  then show ?case sorry
  
qed
  
end
  
