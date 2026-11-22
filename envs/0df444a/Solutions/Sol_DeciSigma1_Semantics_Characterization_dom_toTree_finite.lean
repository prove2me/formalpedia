-- Prove2me | solution 1 for DeciSigma1.Semantics.Characterization.dom_toTree_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:16:12.341538+00:00
-- url     : https://prove2.me/submissions/a2574c97-660f-4ea3-9150-32ef45294ce9

module
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Data.Set.Finite.List
public import Mathlib.Data.Finite.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_bot
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_node
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_top
public import Theorems.Thm_DeciSigma1_Semantics_Tree_bot_le
public import Theorems.Thm_DeciSigma1_Semantics_Tree_le_bot_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_le_top
public import Theorems.Thm_DeciSigma1_Semantics_Tree_node_le_node_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_top_le_iff
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_bot
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_node
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_top
attribute [local simp] DeciSigma1.Semantics.Tree.bot_le
attribute [local simp] DeciSigma1.Semantics.Tree.le_bot_iff
attribute [local simp] DeciSigma1.Semantics.Tree.le_top
attribute [local simp] DeciSigma1.Semantics.Tree.node_le_node_iff
attribute [local simp] DeciSigma1.Semantics.Tree.top_le_iff
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics DeciSigma1.Semantics.Characterization
open DeciSigma1.Semantics.Tree
variable {n : ℕ}
namespace DeciSigma1.Semantics.Characterization
theorem _root_.solution (s : FTree n) : (domain s.toTree).Finite := by
  induction s with
  | bot =>
    apply (Set.finite_singleton ([] : List (Fin n))).subset
    intro π h
    cases π with
    | nil => rfl
    | cons i π => simp [domain] at h
  | top =>
    apply (Set.finite_singleton ([] : List (Fin n))).subset
    intro π h
    cases π with
    | nil => rfl
    | cons i π => simp [domain] at h
  | node a ih =>
    apply ((Set.finite_singleton ([] : List (Fin n))).union
      (Set.finite_iUnion (fun i => (ih i).image (List.cons i)))).subset
    intro π h
    cases π with
    | nil => exact Or.inl rfl
    | cons i π =>
      refine Or.inr (Set.mem_iUnion.mpr ⟨i, π, ?_, rfl⟩)
      simpa [domain] using h
end DeciSigma1.Semantics.Characterization
