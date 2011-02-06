header {* Cayley's Group Representation Theorem *}
theory Cayleys_Theorem
imports Main "~~/src/HOL/Algebra/Bij"
begin

section {* The Cayley Embedding and Cayley Representation Group *}

abbreviation
  Cayley_Embedding :: "('a, 'b) monoid_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("\<phi>\<index>")
  where "\<phi>\<^bsub>G\<^esub> a \<equiv> (\<lambda>x \<in> carrier G.(a \<otimes>\<^bsub>G\<^esub> x))"

abbreviation
  Cay :: "('a, 'b) monoid_scheme \<Rightarrow> ('a \<Rightarrow> 'a) set"
  where "Cay G \<equiv> {(\<phi>\<^bsub>G\<^esub> a) | a. a \<in> (carrier G)}"

--{* Cayley's Representative Subgroup of the Symmetric Group *}
definition
  Cayley :: "('a, 'b) monoid_scheme  \<Rightarrow> ('a \<Rightarrow> 'a) monoid"
  where "Cayley G = BijGroup (carrier G) \<lparr> carrier := Cay G \<rparr>"

--{* We first need to prove lots of statements about identity and composition *}
lemma (in group) id_equiv [simp]: "\<phi> \<one> = (\<lambda>x \<in> carrier G. x)" (is "_ = ?id")
proof -
   have "\<forall>y \<in> carrier G. (\<phi> \<one>) y = ?id y"
     and "(\<phi> \<one>) \<in> extensional (carrier G)"
     and "?id \<in> extensional (carrier G)" by simp+
   thus ?thesis by (fastsimp intro: extensionalityI)
qed

lemma (in group) id_in_Cayley: "(\<lambda>x \<in> carrier G. x) \<in> Cay G"
proof -
  have "(\<phi> \<one>) \<in> Cay G" by fast
  thus ?thesis by (simp add: id_equiv)
qed

lemma (in group) \<phi>_hom [simp]:
  assumes "a \<in> carrier G"
      and "b \<in> carrier G"
    shows "compose (carrier G) (\<phi> a) (\<phi> b) = \<phi> (a\<otimes>b)" (is "?cab = _")
proof -
   let ?cG = "carrier G"
   { fix x; assume "x \<in> ?cG"
     with assms group.axioms m_assoc 
     have "?cab x = \<phi> (a\<otimes>b) x" 
       by (unfold compose_def, simp) }
   moreover have "{?cab, \<phi> (a\<otimes>b)} \<subseteq> extensional ?cG"
     by (simp add: compose_def)
   moreover note extensionalityI 
     [where f="?cab" and g="\<phi> (a\<otimes>b)" and A="?cG"]
   ultimately show ?thesis by fastsimp
qed

lemma (in group) compose_Cay:
  assumes "f \<in> Cay G"
      and "g \<in> Cay G"
    shows "compose (carrier G) f g \<in> Cay G"
using assms
proof -
   from assms obtain a b where
   "{a,b} \<subseteq> carrier G" and "f = (\<phi> a)" and "g = (\<phi> b)"
      by fast+
   thus ?thesis
     by (simp, metis Units_eq Units_m_closed \<phi>_hom restrict_apply)
qed

lemma (in group) inv_Cay:
  assumes "f \<in> Cay G"
    shows "\<exists>g \<in> Cay G. (compose (carrier G) g f) = (\<lambda>x \<in> carrier G. x) \<and>
                       (compose (carrier G) f g) = (\<lambda>x \<in> carrier G. x)"
  using assms
proof -
  let ?cG = "carrier G"
  from assms obtain a b where
  I: "a \<in> ?cG" and  II: "f = \<phi> a" by fast+
  hence III: "inv a \<in> ?cG" by fast
  let ?g = "\<phi> (inv a)"
  from I have "?g \<in> Cay G" by fast
  moreover have "(compose ?cG ?g f) = (\<phi> \<one>)" and
                "(compose ?cG f ?g) = (\<phi> \<one>)" 
                   by (simp add: I II III)+
  ultimately show ?thesis by (simp, fast)
qed

lemma bij_on_inverseI:
   assumes "compose A g f = (\<lambda>x\<in>A .x)"
     shows "bij_betw f A (f ` A)"
using assms
proof -
 { fix x; assume \<heartsuit>: "x \<in> A"
   hence "g (f x) = (compose A g f) x"
    by (simp add: compose_def)
   also from assms \<heartsuit>
   have "\<dots> = x" by simp
   finally have "g (f x) = x" by simp }
 thus ?thesis 
   by (simp add: bij_betw_def, 
       fast intro: inj_on_inverseI)
qed

lemma (in group) image_of_Cayley:
  assumes "f \<in> Cay G"
    shows "f ` (carrier G) = carrier G"
  using assms
proof -
  let ?cG = "carrier G"
  from assms obtain a b where
  I: "a \<in> ?cG" and  II: "f = \<phi> a" by fast+
  hence "f ` ?cG \<subseteq> ?cG" by (fastsimp intro: group.axioms)
  moreover
  { fix x; assume \<heartsuit>: "x \<in> ?cG"
    from I have \<spadesuit>: "(inv a) \<in> ?cG" by fastsimp
    from I II \<heartsuit> \<spadesuit>
         have "f (inv a \<otimes> x) = a \<otimes> ((inv a) \<otimes> x)" by fastsimp
    also from I \<heartsuit> \<spadesuit> m_assoc
         have "\<dots> = (a \<otimes> inv a) \<otimes> x" by fastsimp
    also from I l_inv r_one \<heartsuit>
         have "\<dots> = x" by simp
    ultimately have "f (inv a \<otimes> x) = x" by simp }
   hence "\<forall>x \<in> ?cG. \<exists> y \<in> ?cG . f y = x" by (fastsimp intro: I group.axioms)
   ultimately show ?thesis by fast
qed

lemma (in group) Cay_Bij:
  assumes "f \<in> Cay G"
    shows "f \<in> Bij (carrier G)"
  using assms
proof -
  from assms bij_on_inverseI inv_Cay
  have "bij_betw f (carrier G) (f ` carrier G)" by fast
moreover 
  from assms image_of_Cayley 
  have "f ` (carrier G) = carrier G" by fast
moreover note assms
  ultimately show ?thesis by (simp add: Bij_def, fastsimp)
qed

lemma (in group) Bij_inv_Cay:
  assumes "f \<in> Cay G"
    shows "inv\<^bsub>BijGroup (carrier G)\<^esub> f \<in> Cay G" 
  using assms
proof -
  let ?cG = "carrier G"
  let ?BIJ = "BijGroup ?cG"
  interpret BIJ: group "(?BIJ)" by (rule group_BijGroup)
  from assms inv_Cay 
  obtain g where 
      I:   "g \<in> (Cay G)" and
      II:  "compose ?cG f g = (\<lambda>x\<in>?cG. x)" by fast
  from assms I Cay_Bij have "{f,g} \<subseteq> carrier ?BIJ" by (simp add: BijGroup_def)
  hence 
     III: "{f,g,inv\<^bsub>?BIJ\<^esub> f} \<subseteq> carrier ?BIJ" by fast
  with II have 
      IV: "f \<otimes>\<^bsub>?BIJ\<^esub> g =  \<one>\<^bsub>?BIJ\<^esub>" by (simp add: BijGroup_def)
  from III BIJ.Units BIJ.Units_l_inv have
       V: "inv\<^bsub>?BIJ\<^esub> f \<otimes>\<^bsub>?BIJ\<^esub> f =  \<one>\<^bsub>?BIJ\<^esub>" by auto
  from I III IV V BIJ.inv_unique show ?thesis by fast
qed

lemma (in group) subgroup_Cay:
   "subgroup (Cay G) (BijGroup (carrier G))"
apply (rule subgroup.intro)
  --{*@{term "Cay G \<subseteq> carrier (BijGroup (carrier G))"}*}
    apply (simp add: BijGroup_def)
    apply (fast intro: Cay_Bij)
  --{*@{term "\<And>x y. \<lbrakk>x \<in> Cay G; y \<in> Cay G\<rbrakk> \<Longrightarrow> x \<otimes>\<^bsub>BijGroup (carrier G)\<^esub> y \<in> Cay G"}*}
    apply (simp add: BijGroup_def)
    apply (fastsimp intro: compose_Cay Cay_Bij)
  --{*@{term "\<one>\<^bsub>BijGroup (carrier G)\<^esub> \<in> Cay G"}*}
    apply (simp add: BijGroup_def)
    apply (metis Units_eq id_equiv one_closed)
  --{*@{term "\<And>x. x \<in> Cay G \<Longrightarrow> inv\<^bsub>BijGroup (carrier G)\<^esub> x \<in> Cay G"}*}
    apply (rule Bij_inv_Cay) 
    apply(assumption)
done

theorem (in group) group_Cayley: "group (Cayley G)"
by (simp add: Cayley_def subgroup.subgroup_is_group subgroup_Cay
              group_BijGroup)

lemma (in group) bij_betw_\<phi>:
  "bij_betw \<phi> (carrier G) (carrier (Cayley G))"
proof -
  { fix a b
    assume dom: "{a,b} \<subseteq> carrier G" and
           eq:  "\<phi> a = \<phi> b"
    hence "\<phi> a \<one> = \<phi> b \<one>" by simp
    with dom have "a = b" by simp }
  hence "inj_on \<phi> (carrier G)" 
    by (simp add: inj_on_def)
  thus ?thesis by (simp add: bij_betw_def Cayley_def, fast)
qed

lemma (in group) hom_\<phi>: 
  assumes "x \<in> carrier G" and "y \<in> carrier G"
    shows "\<phi> (x \<otimes> y) = \<phi> x \<otimes>\<^bsub>Cayley G\<^esub> \<phi> y"
using assms
proof -
  from assms Cay_Bij have 
   \<heartsuit>: "{\<phi> x, \<phi> y} \<subseteq> Bij (carrier G)" by fastsimp
  with assms \<phi>_hom have
    "\<phi> (x \<otimes> y) = compose (carrier G) (\<phi> x) (\<phi> y)" by simp
  also from \<heartsuit> have
    "\<dots> = \<phi> x \<otimes>\<^bsub>Cayley G\<^esub> \<phi> y" by (simp add: Cayley_def BijGroup_def)
  ultimately show ?thesis by simp
qed

-- {*Our main result*}

theorem (in group) Cayley_Theorem:
  "\<phi> \<in> G \<cong> (Cayley G)"
by (simp add: iso_def hom_def,
     metis Units_eq bij_betw_\<phi> bij_betw_imp_funcset hom_\<phi>)

end