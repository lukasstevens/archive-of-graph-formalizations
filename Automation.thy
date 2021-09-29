theory Automation
  imports Graph_Theory.Graph_Theory "Auto2_HOL.Auto2_Main"
begin

section \<open>Automation\<close>
text \<open>
  The purpose of this section is to collect use cases for proof automation in the graph library.
\<close>

subsection \<open>Noschinski\<close>

ML \<open>
fun not_trancl s _ (_, inst) =
  let
    val t = (lookup_inst inst s)
  in
    case t of (Const (@{const_name trancl}, _) $ _) => false | _ => true
  end
\<close>

thm trancl_into_rtrancl

declare trancl_into_rtrancl[backward]
declare rtranclD[forward]
ML \<open>
  get_prfsteps (Context.Proof @{context}) |> rev
\<close>
declare reachable_def[rewrite]
lemma rtrancl_onD[forward]: "(a, b) \<in> rtrancl_on A r \<Longrightarrow> a = b \<and> a \<in> A \<and> b \<in> A \<or> a \<noteq> b \<and> (a, b) \<in> r\<^sup>+"
  apply(induction rule: rtrancl_on.induct)
   apply(auto simp: trancl.trancl_into_trancl)
  done
declare rtrancl_refl[resolve]
local_setup \<open>add_forward_prfstep_cond @{thm trancl_trans} (with_conds ["?x \<noteq> ?y", "?y \<noteq> ?x"])\<close>
local_setup \<open>add_forward_prfstep_cond @{thm r_into_trancl} [with_filt (not_trancl "r")]\<close>

context wf_digraph
begin

thm reachable_awalkI reachable_adj_trans adj_reachable_trans reachable_awalk reachable_trans
  reachable1_reachable_trans reachable_reachable1_trans reachable_neq_reachable1
reachable1_reachable reachable_adjI

declare [[show_hyps]]
local_setup \<open>add_forward_prfstep @{thm reachable_awalkI}\<close>

ML \<open>
val b = Normalizer.get_normalizers (Context.Proof @{context})
val a = get_prfsteps (Context.Proof @{context}) |> rev
\<close>
end
ML \<open>
get_prfsteps (Context.Proof @{context}) |> rev
\<close>

lemma (in wf_digraph) "awalk u p v \<Longrightarrow> u \<rightarrow>\<^sup>* v"
  using [[show_hyps]]
  apply(auto2)
  done

print_attributes
lemma (in wf_digraph) "u \<rightarrow>\<^sup>+ v \<Longrightarrow> v \<rightarrow>\<^sup>* y \<Longrightarrow> y \<rightarrow> x \<Longrightarrow> u \<rightarrow>\<^sup>+ x"
  using [[print_trace]]
  apply(auto2)
  done

lemma "(u, v) \<in> r\<^sup>* \<Longrightarrow> (v, y) \<in> r\<^sup>* \<Longrightarrow> (y, x) \<in> r\<^sup>+ \<Longrightarrow> (u, x) \<in> r\<^sup>*"
  using [[print_trace]]
  apply(auto2)
  done


thm rtranclD
lemma (in wf_digraph)
  assumes "awalk u p v" "v \<rightarrow>\<^sup>* y" "y \<rightarrow> x"
  shows "u \<rightarrow>\<^sup>* x"
  using assms
  using [[show_hyps]]

  apply(auto2)
  using assms reachable_adj_trans reachable_awalk reachable_trans
   apply -
  apply metis+
  done


lemma (in wf_digraph)
  assumes  "apath u p1 v" "v \<rightarrow> y" "trail y p2 x"
  shows "\<exists>e. awalk u (p1@e#p2) x"
  using assms
  using reachable_awalk unfolding trail_def apath_def apply(auto) sorry

lemma (in wf_digraph)
  assumes "v \<rightarrow>\<^sup>* y" "y \<rightarrow> x" "x \<rightarrow>\<^sup>+ v"
  shows "\<exists>c. cycle c"
  using assms unfolding cycle_def sorry


lemma (in wf_digraph)
  assumes "awalk u p v" "v \<rightarrow> x" "awalk x (p1#ps1) u"
  shows "\<exists>c. cycle c"
  using assms unfolding cycle_def sorry

lemma (in wf_digraph)
  assumes "v \<rightarrow>\<^sup>* x" "awalk x p y"
  shows "\<mu> w v y < \<infinity>"
  sorry

text \<open>
  In general, the automation does not seem to work so well if you mix reachability and awalks.
\<close>

end
