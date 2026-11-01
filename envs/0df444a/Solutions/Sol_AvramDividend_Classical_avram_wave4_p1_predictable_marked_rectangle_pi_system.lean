-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_predictable_marked_rectangle_pi_system
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T18:55:57.16009+00:00
-- url     : https://prove2.me/submissions/111e06c7-404d-4181-b115-f1315c0ba0d5

import Mathlib
import Mathlib.Probability.Process.Predictable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory MeasurableSpace Set
open scoped ENNReal NNReal

/-- The generating adapted past-measurable future-half-line rectangles are
closed under nonempty pairwise intersections. Taking their Cartesian products
with measurable mark sets preserves this Pi-system property, which is the
finite-intersection step in a genuine predictable marked-kernel monotone-class
extension. -/
theorem solution
    {Ω ι E : Type*} [mΩ : MeasurableSpace Ω]
    [LinearOrder ι] [OrderBot ι] [mE : MeasurableSpace E]
    (𝓕 : Filtration ι mΩ) :
    let G : Set (Set (ι × Ω)) :=
      {S | (∃ A : Set Ω, MeasurableSet[𝓕 ⊥] A ∧
                S = ({⊥} ×ˢ A)) ∨
           (∃ i : ι, ∃ A : Set Ω, MeasurableSet[𝓕 i] A ∧
                S = (Set.Ioi i ×ˢ A))}
    let GM : Set (Set ((ι × Ω) × E)) :=
      Set.image2 (· ×ˢ ·) G {C : Set E | MeasurableSet C}
    IsPiSystem G ∧ IsPiSystem GM := by
  classical
  let G : Set (Set (ι × Ω)) :=
    {S | (∃ A : Set Ω, MeasurableSet[𝓕 ⊥] A ∧
                S = ({⊥} ×ˢ A)) ∨
           (∃ i : ι, ∃ A : Set Ω, MeasurableSet[𝓕 i] A ∧
                S = (Set.Ioi i ×ˢ A))}
  let GM : Set (Set ((ι × Ω) × E)) :=
    Set.image2 (· ×ˢ ·) G {C : Set E | MeasurableSet C}
  change IsPiSystem G ∧ IsPiSystem GM
  have hG : IsPiSystem G := by
    intro s hs t ht hst
    rcases hs with ⟨A, hA, rfl⟩ | ⟨i, A, hA, rfl⟩
    · rcases ht with ⟨B, hB, rfl⟩ | ⟨j, B, hB, rfl⟩
      · left
        refine ⟨A ∩ B, hA.inter hB, ?_⟩
        simp [Set.prod_inter_prod]
      · exfalso
        rcases hst with ⟨p, hp⟩
        have hbot : p.1 = (⊥ : ι) := Set.mem_singleton_iff.mp hp.1.1
        have hj : j < p.1 := hp.2.1
        rw [hbot] at hj
        exact (not_lt_of_ge (bot_le : (⊥ : ι) ≤ j)) hj
    · rcases ht with ⟨B, hB, rfl⟩ | ⟨j, B, hB, rfl⟩
      · exfalso
        rcases hst with ⟨p, hp⟩
        have hbot : p.1 = (⊥ : ι) := Set.mem_singleton_iff.mp hp.2.1
        have hi : i < p.1 := hp.1.1
        rw [hbot] at hi
        exact (not_lt_of_ge (bot_le : (⊥ : ι) ≤ i)) hi
      · by_cases hij : i ≤ j
        · right
          have hAj : MeasurableSet[𝓕 j] A := (𝓕.mono hij) A hA
          refine ⟨j, A ∩ B, hAj.inter hB, ?_⟩
          have hI : Set.Ioi i ∩ Set.Ioi j = Set.Ioi j := by
            ext x
            simp only [Set.mem_inter_iff, Set.mem_Ioi]
            exact ⟨fun hx => hx.2, fun hx => ⟨lt_of_le_of_lt hij hx, hx⟩⟩
          rw [Set.prod_inter_prod, hI]
        · right
          have hji : j ≤ i := le_of_not_ge hij
          have hBi : MeasurableSet[𝓕 i] B := (𝓕.mono hji) B hB
          refine ⟨i, A ∩ B, hA.inter hBi, ?_⟩
          have hI : Set.Ioi i ∩ Set.Ioi j = Set.Ioi i := by
            ext x
            simp only [Set.mem_inter_iff, Set.mem_Ioi]
            exact ⟨fun hx => hx.1, fun hx => ⟨hx, lt_of_le_of_lt hji hx⟩⟩
          rw [Set.prod_inter_prod, hI]
  exact ⟨hG, hG.prod isPiSystem_measurableSet⟩
