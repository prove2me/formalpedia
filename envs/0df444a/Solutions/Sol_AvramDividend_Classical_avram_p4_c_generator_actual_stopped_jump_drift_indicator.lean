-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_actual_stopped_jump_drift_indicator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:39:05.81657+00:00
-- url     : https://prove2.me/submissions/a871e051-0847-4cc8-9671-3d1a450e9f16

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The literal original ruin-stopped jump-generator drift equals the
interior-event indicator of the source negative-mark integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (a b : ℝ) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let A : Set (ℝ≥0 × Ω) :=
      {p | (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 ∧ Y p ∈ Icc a b}
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc a b then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    ∀ p : ℝ≥0 × Ω,
      (∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν) =
      A.indicator (fun p => ∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand w (Y p) z ∂X.ν) p := by
  intro Y A JG p
  by_cases hs : (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2
  · by_cases hb : Y p ∈ Icc a b
    · have hp : p ∈ A := ⟨hs, hb⟩
      have hj : (fun z : ℝ => JG (p, z)) =
          (fun z => SpectrallyNegativeLevy.generatorIntegrand w (Y p) z) := by
        funext z
        simp only [JG, if_pos hs, if_pos hb, one_mul]
      simp only [Set.indicator_of_mem hp]
      rw [hj]
    · have hp : p ∉ A := by
        intro hh
        exact hb hh.2
      have hj : (fun z : ℝ => JG (p, z)) =
          (fun _ : ℝ => (0 : ℝ)) := by
        funext z
        simp only [JG, if_pos hs, if_neg hb, mul_zero]
      simp only [Set.indicator_of_notMem hp]
      rw [hj]
      simp
  · have hp : p ∉ A := by
      intro hh
      exact hs hh.1
    have hj : (fun z : ℝ => JG (p, z)) =
        (fun _ : ℝ => (0 : ℝ)) := by
      funext z
      simp only [JG, if_neg hs, zero_mul]
    simp only [Set.indicator_of_notMem hp]
    rw [hj]
    simp
