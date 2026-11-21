-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_original_true_future_fullmark_past_predictable_cross_mean_zero_proved
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T10:07:45.140355+00:00
-- url     : https://prove2.me/submissions/0dec57c5-6410-4ec4-97a4-ff6ffab5e002

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_rightcont_conditional_L2_exact
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_past_coefficient_future_fullmark_condExp_zero_cross
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original full negative Lévy mark count on a future physical cell
is orthogonal to any integrable true past-predictable coefficient. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0) (n : ℕ) :
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    ∀ (U : Ω → ℝ),
      StronglyMeasurable[𝓕.rightCont s] U →
      Integrable (fun ω => U ω * ((N ω).toReal - r)) P →
      Integrable (fun ω => (N ω).toReal - r) P →
      (∫ ω, U ω * ((N ω).toReal - r) ∂P) = 0 := by
  intro B N r U hU hUI hNI
  have hMean : P[(fun ω => (N ω).toReal - r) |
      𝓕.rightCont s] =ᵐ[P] (fun _ => 0) := by
    simpa only [N, r, B] using
      (avram_p4_s3_interval_h_original_full_cutoff_rightcont_conditional_L2_exact
        X s T n).1
  exact avram_pj_original_past_coefficient_future_fullmark_condExp_zero_cross
    (𝓕.rightCont s) (𝓕.rightCont.le s)
    U (fun ω => (N ω).toReal - r) hU hUI hNI hMean
