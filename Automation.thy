theory Automation
  imports Graph_Theory.Graph_Theory "Auto2_HOL.Auto2_Main"
begin

section \<open>Automation\<close>
text \<open>
  The purpose of this section is to collect use cases for proof automation in the graph library.
\<close>

subsection \<open>Noschinski\<close>

context wf_digraph
begin


lemma dominates_awalk: "u \<rightarrow> v \<longleftrightarrow> (\<exists>e. awalk u [e] v)"
  by (metis arc_implies_awalk awalk_Cons_iff awalk_empty_ends in_arcs_imp_in_arcs_ends reachableE)

lemma reachable1_awalk': "u \<rightarrow>\<^sup>+ v \<longleftrightarrow> (\<exists>e es. awalk u (e # es) v)"
proof 
  assume "u \<rightarrow>\<^sup>+ v"
  then show "\<exists>e es. awalk u (e # es) v"
    apply(induction rule: trancl_induct)
    by (metis dominates_awalk awalk_Cons_iff reachable_adj_trans reachable_awalk)+
next
  assume "\<exists>e es. awalk u (e # es) v"
  then show "u \<rightarrow>\<^sup>+ v"
    using reachable1_awalk by auto
qed

lemma awalk_empty: "u \<in> verts G \<Longrightarrow> awalk u [] u"
  using awalk_empty_ends awalk_Nil_iff by blast

lemma cycle_awalkI: "awalk u (e # es) u \<Longrightarrow> \<exists>c. cycle c"
  using closed_w_imp_cycle[of "e # es"] unfolding closed_w_def by blast

local_setup \<open>add_resolve_prfstep @{thm awalk_empty}\<close>
local_setup \<open>add_forward_prfstep_cond @{thm awalk_appendI} (with_conds ["?u \<noteq> ?v", "?v \<noteq> ?w"])\<close>
local_setup \<open>add_forward_prfstep @{thm arc_implies_awalk}\<close>
local_setup \<open>add_rewrite_rule @{thm dominates_awalk}\<close>
local_setup \<open>add_rewrite_rule @{thm reachable1_awalk'}\<close>
local_setup \<open>add_rewrite_rule @{thm reachable_awalk}\<close>
local_setup \<open>add_rewrite_rule @{thm apath_def}\<close>
local_setup \<open>add_rewrite_rule @{thm trail_def}\<close>
local_setup \<open>add_resolve_prfstep @{thm cycle_awalkI}\<close>
local_setup \<open>add_rewrite_rule @{thm \<mu>_reach_conv}\<close>

end

context wf_digraph
begin
ML \<open>
get_prfsteps (Context.Proof @{context}) |> filter (fn p => match_string "reachable*" (#name p))
\<close>

end

declare [[show_hyps]]

lemma (in wf_digraph) "u \<rightarrow>\<^sup>+ v \<Longrightarrow> v \<rightarrow>\<^sup>* y \<Longrightarrow> y \<rightarrow> x \<Longrightarrow> u \<rightarrow>\<^sup>+ x"
  using [[print_trace, show_hyps]]
  apply(auto2)
  done

lemma (in wf_digraph)
  assumes "awalk u p v" "v \<rightarrow>\<^sup>+ y" "y \<rightarrow> x"
  shows "u \<rightarrow>\<^sup>* x"
  using assms
  apply -
  using [[show_hyps, print_trace]]
  apply auto2 done

lemma (in wf_digraph)
  assumes "apath u p1 v" "v \<rightarrow> y" "trail y p2 x"
  shows "\<exists>e. awalk u (p1@e#p2) x"
  using assms apply -
@proof
@qed
(* This works: apply(auto2) done *)

lemma (in wf_digraph)
  assumes "v \<rightarrow>\<^sup>* y" "y \<rightarrow> x" "x \<rightarrow>\<^sup>+ v"
  shows "\<exists>c. cycle c"
  using assms
  apply(auto2)
  done


lemma (in wf_digraph)
  assumes "awalk u p v" "v \<rightarrow> x" "awalk x (p1#ps1) u"
  shows "\<exists>c. cycle c"
  using assms
  apply(auto2)
  done
  

lemma (in wf_digraph)
  assumes "v \<rightarrow>\<^sup>* x" "awalk x p y"
  shows "\<mu> w v y < \<infinity>"
  using assms
  apply(auto2)
  done

end
