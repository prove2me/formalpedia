-- Prove2me | solution 1 for DeciSigma1.Constraints.TopFree.holdsT_toLitT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:23:35.337575+00:00
-- url     : https://prove2.me/submissions/2a2ce8ea-a30f-4d28-a349-35a36efc0c18

module
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Embedding
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Transfer
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Set.Finite.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Guard
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_node
public import Theorems.Thm_DeciSigma1_Semantics_PrefixSet_toTree_eq_bot_iff
public import Theorems.Thm_DeciSigma1_Semantics_PrefixSet_toTree_le_toTree
public import Theorems.Thm_DeciSigma1_Semantics_PrefixSet_toTree_node
public import Theorems.Thm_DeciSigma1_Semantics_treeLe_false_iff_le
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_node
attribute [local simp] DeciSigma1.Semantics.PrefixSet.toTree_eq_bot_iff
attribute [local simp] DeciSigma1.Semantics.PrefixSet.toTree_le_toTree
attribute [local simp] DeciSigma1.Semantics.treeLe_false_iff_le



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints DeciSigma1.Constraints.TopFree
open DeciSigma1.Semantics
variable {n : ℕ} {V : Type}
namespace DeciSigma1.Constraints.TopFree
theorem _root_.solution (ρ : V → PrefixSet n) (l : Lit n V) :
    HoldsT (fun _ => false) (fun v => (ρ v).toTree) l.toLitT ↔ l.Holds ρ := by
  have hn (a : Fin n → V) :
      Semantics.Tree.node ((fun v => (ρ v).toTree) ∘ a) = (PrefixSet.node (ρ ∘ a)).toTree :=
    (PrefixSet.toTree_node _).symm
  cases l with
  | le u v => exact (treeLe_false_iff_le _ _).trans (PrefixSet.toTree_le_toTree _ _)
  | fLe a u =>
    exact (treeLe_false_iff_le _ _).trans ((hn a).symm ▸ PrefixSet.toTree_le_toTree _ _)
  | leF u a =>
    exact (treeLe_false_iff_le _ _).trans ((hn a).symm ▸ PrefixSet.toTree_le_toTree _ _)
  | eqBot u => exact PrefixSet.toTree_eq_bot_iff _
end DeciSigma1.Constraints.TopFree
