-- Prove2me | solution 1 for AvramDividend.Classical.bv_binary_patterns_pairwise_disjoint_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T00:26:54.658016+00:00
-- url     : https://prove2.me/submissions/28847b5c-592d-48d2-a56b-51ae490784ea

import Mathlib.Data.Finset.Powerset

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped Classical

/-- Distinct complete binary grid patterns are disjoint as sample events. -/
theorem solution
    {Ω : Type*} (A B : ℕ → Set Ω) (n k : ℕ)
    (hExcl : ∀ i : ℕ, i < n → ∀ ω : Ω,
      ω ∈ A i → ω ∈ B i → False) :
    ((↑(Finset.powersetCard k (Finset.range n))) : Set (Finset ℕ)).PairwiseDisjoint
      (fun S => {ω : Ω | ∀ i : ℕ, i < n →
        if i ∈ S then ω ∈ A i else ω ∈ B i}) := by
  classical
  intro S hS T hT hST
  apply Set.disjoint_left.mpr
  intro ω hωS hωT
  obtain ⟨hSubS, _⟩ := Finset.mem_powersetCard.mp hS
  obtain ⟨hSubT, _⟩ := Finset.mem_powersetCard.mp hT
  have hPatternActive (U : Finset ℕ)
      (hU : ∀ i : ℕ, i < n →
        if i ∈ U then ω ∈ A i else ω ∈ B i)
      (i : ℕ) (hi : i < n) :
      i ∈ U ↔ ω ∈ A i := by
    by_cases hMem : i ∈ U
    · have ha : ω ∈ A i := by simpa [hMem] using hU i hi
      simp [hMem, ha]
    · have hb : ω ∈ B i := by simpa [hMem] using hU i hi
      have hna : ω ∉ A i := fun ha => hExcl i hi ω ha hb
      simp [hMem, hna]
  have hEq : S = T := by
    ext i
    by_cases hi : i < n
    · exact (hPatternActive S hωS i hi).trans
        (hPatternActive T hωT i hi).symm
    · have hns : i ∉ S := fun hs =>
        hi (Finset.mem_range.mp (hSubS hs))
      have hnt : i ∉ T := fun ht =>
        hi (Finset.mem_range.mp (hSubT ht))
      simp [hns, hnt]
  exact hST hEq
