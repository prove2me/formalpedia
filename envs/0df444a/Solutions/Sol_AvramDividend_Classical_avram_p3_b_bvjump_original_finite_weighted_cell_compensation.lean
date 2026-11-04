-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_finite_weighted_cell_compensation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:31:50.69554+00:00
-- url     : https://prove2.me/submissions/4f091be1-6666-4c3a-a624-fc5d9078d8c9

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (M N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hRect : ∀ (s t : ℝ≥0), s ≤ t →
      ∀ (A : Set Ω), MeasurableSet[𝓕 s] A →
      ∀ (B : Set ℝ), MeasurableSet B →
        M ((Ioc s t ×ˢ A) ×ˢ B) =
        N ((Ioc s t ×ˢ A) ×ˢ B))
    (S : Finset ℕ) (s t : ℕ → ℝ≥0)
    (A : ℕ → Set Ω) (B : ℕ → Set ℝ)
    (c : ℕ → ℝ≥0∞)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (hA : ∀ i ∈ S, MeasurableSet[𝓕 (s i)] (A i))
    (hB : ∀ i ∈ S, MeasurableSet (B i)) :
    (∑ i ∈ S, c i * M ((Ioc (s i) (t i) ×ˢ A i) ×ˢ B i)) =
      (∑ i ∈ S, c i * N ((Ioc (s i) (t i) ×ˢ A i) ×ˢ B i)) := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [hRect (s i) (t i) (hst i hi) (A i) (hA i hi) (B i) (hB i hi)]
