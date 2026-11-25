-- Prove2me | solution 1 for ErdosPosa.IsMax023.fvs_or_pack
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:39:05.962792+00:00
-- url     : https://prove2.me/submissions/a2678a15-b6f4-4857-8847-82b9dfe4385f

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPMaximal
public import Definitions.Def_ErdosPosaLib_EPPin
public import Theorems.Thm_ErdosPosa_IsMax023_pin
public import Theorems.Thm_ErdosPosa_cyc_mono
public import Theorems.Thm_ErdosPosa_exists_minCyc
public import Theorems.Thm_ErdosPosa_pairwise_disjoint_cons
public import Theorems.Thm_ErdosPosa_restr_adj
attribute [local simp] ErdosPosa.restr_adj



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
variable [Finite V] {G H : SimpleGraph V}
namespace ErdosPosa
namespace IsMax023
theorem _root_.solution (hH : IsMax023 G H) : ∀ (j : ℕ) (A : Set V),
    (∀ v ∈ A, deg H v ≠ 3) →
    (∃ F : Fin (j + 1) → Set V, Pairwise (fun i i' => Disjoint (F i) (F i')) ∧
      (∀ i, F i ⊆ A) ∧ ∀ i, Cyc G (F i)) ∨
    ∃ Z : Finset V, Z.card ≤ j ∧ ¬ Cyc G (A \ ↑Z) := by
  classical
  intro j
  induction j with
  | zero =>
    intro A hA
    by_cases hc : Cyc G A
    · obtain ⟨S, hSA, hS, -⟩ := hH.pin hA hc
      refine Or.inl ⟨fun _ => S, ?_, fun _ => hSA, fun _ => hS⟩
      intro i i' hii'
      exact absurd (Fin.ext (by have := i.2; have := i'.2; omega)) hii'
    · exact Or.inr ⟨∅, by simp, by simpa using hc⟩
  | succ j ih =>
    intro A hA
    by_cases hc : Cyc G A
    · obtain ⟨S, hSA, hS, z, hzS, hpin⟩ := hH.pin hA hc
      rcases ih (A \ S) (fun v hv => hA v hv.1) with ⟨F, hF, hFA, hFc⟩ | ⟨Z, hZ, hZc⟩
      · refine Or.inl ⟨Fin.cons S F, ?_, ?_, ?_⟩
        · refine pairwise_disjoint_cons _ _ hF ?_
          intro i
          exact Set.disjoint_of_subset_right (hFA i) Set.disjoint_sdiff_right
        · intro i
          induction i using Fin.cases with
          | zero => simpa using hSA
          | succ i => simpa using (hFA i).trans Set.sdiff_subset
        · intro i
          induction i using Fin.cases with
          | zero => simpa using hS
          | succ i => simpa using hFc i
      · refine Or.inr ⟨insert z Z, (Finset.card_insert_le _ _).trans (by omega), ?_⟩
        intro hc'
        obtain ⟨T, hTsub, hT⟩ := exists_minCyc hc'
        have hTA : T ⊆ A := fun y hy => (hTsub hy).1
        by_cases hTS : ∃ x, x ∈ T ∧ x ∈ S
        · have hzT := hpin T hTA hT hTS
          exact (hTsub hzT).2 (by simp)
        · push Not at hTS
          apply hZc
          refine cyc_mono hT.1 le_rfl ?_
          intro y hy
          refine ⟨⟨(hTsub hy).1, hTS y hy⟩, ?_⟩
          intro hyZ
          exact (hTsub hy).2 (by simp [hyZ])
    · exact Or.inr ⟨∅, by simp, by simpa using hc⟩
end IsMax023
end ErdosPosa
