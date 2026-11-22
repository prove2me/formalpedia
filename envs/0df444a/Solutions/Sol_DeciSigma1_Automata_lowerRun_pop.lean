-- Prove2me | solution 1 for DeciSigma1.Automata.lowerRun_pop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:37:34.37881+00:00
-- url     : https://prove2.me/submissions/763f87e6-7112-49b4-9889-cf8506ddebf4

module
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Theorems.Thm_DeciSigma1_Automata_derivedPairs_trans
public import Theorems.Thm_DeciSigma1_Automata_mem_down
public import Theorems.Thm_DeciSigma1_Automata_mem_lowerStep
public import Theorems.Thm_DeciSigma1_Automata_lowerRun_snoc
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Constraints_holdsT_map
public import Theorems.Thm_DeciSigma1_Constraints_holds_false
public import Theorems.Thm_DeciSigma1_Constraints_lowerAt_nil_iff
public import Theorems.Thm_DeciSigma1_Constraints_mem_derivedPairs
public import Theorems.Thm_DeciSigma1_Constraints_sat_false
public import Theorems.Thm_DeciSigma1_Constraints_upperAt_nil_iff
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_bot
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_dual
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_node
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_normalize
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_top
public import Theorems.Thm_DeciSigma1_Semantics_Tree_bot_le
public import Theorems.Thm_DeciSigma1_Semantics_Tree_descend_bot
public import Theorems.Thm_DeciSigma1_Semantics_Tree_descend_node
public import Theorems.Thm_DeciSigma1_Semantics_Tree_descend_top
public import Theorems.Thm_DeciSigma1_Semantics_Tree_hasLabel_bot
public import Theorems.Thm_DeciSigma1_Semantics_Tree_hasLabel_nil
public import Theorems.Thm_DeciSigma1_Semantics_Tree_hasLabel_top
public import Theorems.Thm_DeciSigma1_Semantics_Tree_le_bot_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_le_top
public import Theorems.Thm_DeciSigma1_Semantics_Tree_node_le_node_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_top_le_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_bot
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_cons
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_nil
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_top
public import Theorems.Thm_DeciSigma1_Semantics_bot_treeLe
public import Theorems.Thm_DeciSigma1_Semantics_dual_bot
public import Theorems.Thm_DeciSigma1_Semantics_dual_fn
public import Theorems.Thm_DeciSigma1_Semantics_dual_involutive
public import Theorems.Thm_DeciSigma1_Semantics_dual_le_iff
public import Theorems.Thm_DeciSigma1_Semantics_dual_node
public import Theorems.Thm_DeciSigma1_Semantics_dual_top
public import Theorems.Thm_DeciSigma1_Semantics_node_treeLe_node_iff
public import Theorems.Thm_DeciSigma1_Semantics_normalize_bot
public import Theorems.Thm_DeciSigma1_Semantics_normalize_false_variance
public import Theorems.Thm_DeciSigma1_Semantics_normalize_fn
public import Theorems.Thm_DeciSigma1_Semantics_normalize_involutive
public import Theorems.Thm_DeciSigma1_Semantics_normalize_node
public import Theorems.Thm_DeciSigma1_Semantics_normalize_top
public import Theorems.Thm_DeciSigma1_Semantics_normalize_true
public import Theorems.Thm_DeciSigma1_Semantics_top_treeLe_iff
public import Theorems.Thm_DeciSigma1_Semantics_treeLe_bot_iff
public import Theorems.Thm_DeciSigma1_Semantics_treeLe_false_iff_le
public import Theorems.Thm_DeciSigma1_Semantics_treeLe_top
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Constraints.holdsT_map
attribute [local simp] DeciSigma1.Constraints.holds_false
attribute [local simp] DeciSigma1.Constraints.lowerAt_nil_iff
attribute [local simp] DeciSigma1.Constraints.sat_false
attribute [local simp] DeciSigma1.Constraints.upperAt_nil_iff
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_bot
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_dual
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_node
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_normalize
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_top
attribute [local simp] DeciSigma1.Semantics.Tree.bot_le
attribute [local simp] DeciSigma1.Semantics.Tree.descend_bot
attribute [local simp] DeciSigma1.Semantics.Tree.descend_node
attribute [local simp] DeciSigma1.Semantics.Tree.descend_top
attribute [local simp] DeciSigma1.Semantics.Tree.hasLabel_bot
attribute [local simp] DeciSigma1.Semantics.Tree.hasLabel_nil
attribute [local simp] DeciSigma1.Semantics.Tree.hasLabel_top
attribute [local simp] DeciSigma1.Semantics.Tree.le_bot_iff
attribute [local simp] DeciSigma1.Semantics.Tree.le_top
attribute [local simp] DeciSigma1.Semantics.Tree.node_le_node_iff
attribute [local simp] DeciSigma1.Semantics.Tree.top_le_iff
attribute [local simp] DeciSigma1.Semantics.Tree.trace_bot
attribute [local simp] DeciSigma1.Semantics.Tree.trace_cons
attribute [local simp] DeciSigma1.Semantics.Tree.trace_nil
attribute [local simp] DeciSigma1.Semantics.Tree.trace_top
attribute [local simp] DeciSigma1.Semantics.bot_treeLe
attribute [local simp] DeciSigma1.Semantics.dual_bot
attribute [local simp] DeciSigma1.Semantics.dual_fn
attribute [local simp] DeciSigma1.Semantics.dual_involutive
attribute [local simp] DeciSigma1.Semantics.dual_le_iff
attribute [local simp] DeciSigma1.Semantics.dual_node
attribute [local simp] DeciSigma1.Semantics.dual_top
attribute [local simp] DeciSigma1.Semantics.node_treeLe_node_iff
attribute [local simp] DeciSigma1.Semantics.normalize_bot
attribute [local simp] DeciSigma1.Semantics.normalize_false_variance
attribute [local simp] DeciSigma1.Semantics.normalize_fn
attribute [local simp] DeciSigma1.Semantics.normalize_involutive
attribute [local simp] DeciSigma1.Semantics.normalize_node
attribute [local simp] DeciSigma1.Semantics.normalize_top
attribute [local simp] DeciSigma1.Semantics.normalize_true
attribute [local simp] DeciSigma1.Semantics.top_treeLe_iff
attribute [local simp] DeciSigma1.Semantics.treeLe_bot_iff
attribute [local simp] DeciSigma1.Semantics.treeLe_false_iff_le
attribute [local simp] DeciSigma1.Semantics.treeLe_top
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


attribute [local simp] DeciSigma1.Automata.mem_down
attribute [local simp] DeciSigma1.Automata.mem_lowerStep
attribute [local simp] DeciSigma1.Automata.lowerRun_snoc

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1
open DeciSigma1.Constraints
open DeciSigma1.Automata
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
namespace DeciSigma1.Automata
theorem _root_.solution {Γ : List (LitT n V)} {bs : Fin n → V} {y a : V} {w : List (Fin n)} (c : Fin n)
    (hu : LitT.leF y bs ∈ Γ) (h : a ∈ lowerRun Γ y (c :: w)) :
    a ∈ lowerRun Γ (bs c) w := by
  induction w using List.reverseRecOn generalizing a with
  | nil =>
    obtain ⟨r, hr, as, hl, hd⟩ := mem_lowerStep.mp h
    exact mem_down.mpr (derivedPairs_trans hd ((mem_derivedPairs Γ _ _).mpr
      (.decomp c hl ((mem_derivedPairs Γ _ _).mp (mem_down.mp hr)) hu)))
  | append_singleton w d ih =>
    change a ∈ lowerRun Γ y ((c :: w) ++ [d]) at h
    rw [lowerRun_snoc, mem_lowerStep] at h ⊢
    obtain ⟨r, hr, as, hl, hd⟩ := h
    exact ⟨r, ih hr, as, hl, hd⟩
end DeciSigma1.Automata
