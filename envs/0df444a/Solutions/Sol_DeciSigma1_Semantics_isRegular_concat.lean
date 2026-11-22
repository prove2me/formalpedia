-- Prove2me | solution 1 for DeciSigma1.Semantics.isRegular_concat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:16:49.724222+00:00
-- url     : https://prove2.me/submissions/1d4b6741-6ce9-4a46-8660-c2622619061f

module
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Data.Set.Finite.List
public import Mathlib.Data.Finite.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Theorems.Thm_DeciSigma1_Semantics_residual_append
public import Theorems.Thm_DeciSigma1_Semantics_isRegular_of_closed
public import Theorems.Thm_DeciSigma1_Semantics_residual_mul
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
theorem _root_.solution {A B : Language n} (ha : IsRegular A) (hb : IsRegular B) :
    IsRegular (concat A B) := by
  classical
  let R := Set.range (residual B)
  let F : Set (Language n) := Set.image2 (fun a T =>
    concat a B ∪ ⋃₀ T) (Set.range (residual A)) (𝒫 R)
  apply isRegular_of_closed (ha.image2 _ hb.powerset) (F := F)
  · exact ⟨A, ⟨[], rfl⟩, ∅, Set.empty_subset _, by simp⟩
  · rintro L ⟨a, ⟨u,rfl⟩, T, hT, rfl⟩ c
    let T' : Set (Language n) := (fun l => residual l [c]) '' T ∪
      (if [] ∈ residual A u then {residual B [c]} else ∅)
    refine ⟨residual A (u ++ [c]), ⟨u ++ [c],rfl⟩, T', ?_, ?_⟩
    · rintro L (⟨l,hl,rfl⟩ | hl)
      · obtain ⟨v,rfl⟩ := hT hl
        exact ⟨v ++ [c], residual_append _ _ _⟩
      · by_cases he : [] ∈ residual A u
        · simp only [he, ite_true, Set.mem_singleton_iff] at hl
          exact hl ▸ ⟨[c], rfl⟩
        · simp [he] at hl
    · rw [residual_append]
      have hq : residual ((concat (residual A u) B ∪ ⋃₀ T)) [c] =
          residual (concat (residual A u) B) [c] ∪
            ⋃₀ ((fun l => residual l [c]) '' T) := by
        ext v; simp [residual]
      rw [hq, residual_mul]
      dsimp only [T']
      rw [Set.sUnion_union]
      ext v
      by_cases he : [] ∈ residual A u <;> simp [he, or_assoc, or_left_comm, or_comm]
end DeciSigma1.Semantics
