-- Prove2me | solution 1 for DeciSigma1.Semantics.le_iff_forall_hasLabel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:16:54.935879+00:00
-- url     : https://prove2.me/submissions/f955b910-0968-4cb7-9219-ef2c7a006d35

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
public import Theorems.Thm_DeciSigma1_Semantics_normalize_fn
public import Theorems.Thm_DeciSigma1_Semantics_normalize_involutive
public import Theorems.Thm_DeciSigma1_Semantics_normalize_bot
public import Theorems.Thm_DeciSigma1_Semantics_normalize_top
public import Theorems.Thm_DeciSigma1_Semantics_normalize_node
public import Theorems.Thm_DeciSigma1_Semantics_normalize_false_variance
public import Theorems.Thm_DeciSigma1_Semantics_dual_fn
public import Theorems.Thm_DeciSigma1_Semantics_dual_involutive
public import Theorems.Thm_DeciSigma1_Semantics_dual_bot
public import Theorems.Thm_DeciSigma1_Semantics_dual_top
public import Theorems.Thm_DeciSigma1_Semantics_dual_node
public import Theorems.Thm_DeciSigma1_Semantics_normalize_true
public import Theorems.Thm_DeciSigma1_Semantics_dual_le_iff
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_normalize
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_dual
public import Theorems.Thm_DeciSigma1_Semantics_Tree_descend_bot
public import Theorems.Thm_DeciSigma1_Semantics_Tree_descend_top
public import Theorems.Thm_DeciSigma1_Semantics_Tree_descend_node
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_nil
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_cons
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_bot
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_top
public import Theorems.Thm_DeciSigma1_Semantics_Tree_hasLabel_nil
public import Theorems.Thm_DeciSigma1_Semantics_Tree_hasLabel_bot
public import Theorems.Thm_DeciSigma1_Semantics_Tree_hasLabel_top
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_eq_bot_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_eq_top_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_not_le_iff_unsafe
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_bot
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_node
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_top
public import Theorems.Thm_DeciSigma1_Semantics_Tree_bot_le
public import Theorems.Thm_DeciSigma1_Semantics_Tree_le_bot_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_le_top
public import Theorems.Thm_DeciSigma1_Semantics_Tree_node_le_node_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_top_le_iff
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_bot
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_node
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_top
attribute [local simp] DeciSigma1.Semantics.Tree.bot_le
attribute [local simp] DeciSigma1.Semantics.Tree.le_bot_iff
attribute [local simp] DeciSigma1.Semantics.Tree.le_top
attribute [local simp] DeciSigma1.Semantics.Tree.node_le_node_iff
attribute [local simp] DeciSigma1.Semantics.Tree.top_le_iff


attribute [local simp] DeciSigma1.Semantics.normalize_fn
attribute [local simp] DeciSigma1.Semantics.normalize_involutive
attribute [local simp] DeciSigma1.Semantics.normalize_bot
attribute [local simp] DeciSigma1.Semantics.normalize_top
attribute [local simp] DeciSigma1.Semantics.normalize_node
attribute [local simp] DeciSigma1.Semantics.normalize_false_variance
attribute [local simp] DeciSigma1.Semantics.dual_fn
attribute [local simp] DeciSigma1.Semantics.dual_involutive
attribute [local simp] DeciSigma1.Semantics.dual_bot
attribute [local simp] DeciSigma1.Semantics.dual_top
attribute [local simp] DeciSigma1.Semantics.dual_node
attribute [local simp] DeciSigma1.Semantics.normalize_true
attribute [local simp] DeciSigma1.Semantics.dual_le_iff
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_normalize
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_dual
attribute [local simp] DeciSigma1.Semantics.Tree.descend_bot
attribute [local simp] DeciSigma1.Semantics.Tree.descend_top
attribute [local simp] DeciSigma1.Semantics.Tree.descend_node
attribute [local simp] DeciSigma1.Semantics.Tree.trace_nil
attribute [local simp] DeciSigma1.Semantics.Tree.trace_cons
attribute [local simp] DeciSigma1.Semantics.Tree.trace_bot
attribute [local simp] DeciSigma1.Semantics.Tree.trace_top
attribute [local simp] DeciSigma1.Semantics.Tree.hasLabel_nil
attribute [local simp] DeciSigma1.Semantics.Tree.hasLabel_bot
attribute [local simp] DeciSigma1.Semantics.Tree.hasLabel_top

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}
namespace DeciSigma1.Semantics
theorem _root_.solution (t u : Tree n) :
    t ≤ u ↔ ∀ π, (t.HasLabel π .top → u.HasLabel π .top) ∧
      (u.HasLabel π .bot → t.HasLabel π .bot) := by
  have h := Tree.not_le_iff_unsafe t u
  simp only [ne_eq, Tree.trace_eq_bot_iff, Tree.trace_eq_top_iff] at h
  classical
  constructor
  · intro hle π
    constructor
    · intro ht
      by_contra hu
      exact (h.mpr ⟨π, Or.inr ⟨ht, hu⟩⟩) hle
    · intro hu
      by_contra ht
      exact (h.mpr ⟨π, Or.inl ⟨ht, hu⟩⟩) hle
  · intro hs
    by_contra hn
    obtain ⟨π, ⟨ht, hu⟩ | ⟨ht, hu⟩⟩ := h.mp hn
    · exact ht ((hs π).2 hu)
    · exact hu ((hs π).1 ht)
end DeciSigma1.Semantics
