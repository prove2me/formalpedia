-- Prove2me | solution 1 for DeciSigma1.Semantics.residual_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:16:11.707734+00:00
-- url     : https://prove2.me/submissions/5c25772a-b1f4-423a-976c-97eebc99fc4e

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
open DeciSigma1 DeciSigma1.Semantics
open DeciSigma1.Automata
variable {n : ℕ}
namespace DeciSigma1.Semantics
theorem _root_.solution (A B : Language n) (c : Fin n) :
    residual (concat A B) [c] =
      concat (residual A [c]) B ∪
        {v | [] ∈ A ∧ c :: v ∈ B} := by
  classical
  ext v
  constructor
  · rintro ⟨a, ha, b, hb, he⟩
    cases a with
    | nil =>
      right
      simp only [List.nil_append] at he
      subst b
      exact ⟨ha, hb⟩
    | cons d a =>
      have he' := List.cons.inj he
      obtain ⟨rfl, rfl⟩ := he'
      exact Or.inl ⟨a, ha, b, hb, rfl⟩
  · rintro (⟨a, ha, b, hb, rfl⟩ | h)
    · exact ⟨c :: a, ha, b, hb, rfl⟩
    · exact ⟨[], h.1, c :: v, h.2, rfl⟩
end DeciSigma1.Semantics
