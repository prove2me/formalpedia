-- Prove2me | solution 1 for DeciSigma1.Semantics.Tree.descend_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:02:17.341809+00:00
-- url     : https://prove2.me/submissions/a8afbe17-5aa0-4408-ada9-82aad4e07a75

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

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}
open DeciSigma1.Semantics.Tree
namespace DeciSigma1.Semantics.Tree
theorem _root_.solution (i : Fin n) : descend Tree.bot i = Tree.bot := by
  simp [descend]
end DeciSigma1.Semantics.Tree
