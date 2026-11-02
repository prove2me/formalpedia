-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_original_C1_source_drift_expectation_right_slope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:43:19.696548+00:00
-- url     : https://prove2.me/submissions/2001d4b8-99f6-4c63-8678-842a25bcabc8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_original_C1_source_drift_pointwise
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! Bounded-convergence transfer of the moving-base drift derivative
along the exact original source process, with no C2 regularity. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x d : ℝ) :
    Tendsto (fun h : ℝ =>
      ∫ ω, h⁻¹ *
        (w (x + X.X (Real.toNNReal h) ω) -
         w (x + X.X (Real.toNNReal h) ω - d * h)) ∂P)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (d * deriv w x)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let Q : ℝ → Ω → ℝ := fun h ω => h⁻¹ *
    (w (x + X.X (Real.toNNReal h) ω) -
     w (x + X.X (Real.toNNReal h) ω - d * h))
  have hmeas (h : ℝ) : AEStronglyMeasurable (Q h) P := by
    have hXm : Measurable (X.X (Real.toNNReal h)) :=
      (X.adapted (Real.toNNReal h)).mono (𝓕.le (Real.toNNReal h)) le_rfl
    have hA : Measurable (fun ω => x + X.X (Real.toNNReal h) ω) :=
      measurable_const.add hXm
    have hB : Measurable (fun ω => x + X.X (Real.toNNReal h) ω - d * h) :=
      hA.sub measurable_const
    exact (measurable_const.mul
      ((hwC1.continuous.measurable.comp hA).sub
       (hwC1.continuous.measurable.comp hB))).aestronglyMeasurable
  have hbound (h : ℝ) : ∀ᵐ ω ∂P, ‖Q h ω‖ ≤ L * |d| := by
    filter_upwards [] with ω
    by_cases hh : h = 0
    · simp [Q, hh]
      exact mul_nonneg hL (abs_nonneg d)
    · have hk := hLip (x + X.X (Real.toNNReal h) ω)
        (x + X.X (Real.toNNReal h) ω - d * h)
      have hdif : |(x + X.X (Real.toNNReal h) ω) -
          (x + X.X (Real.toNNReal h) ω - d * h)| = |d * h| := by
        congr 1
        ring
      have hinv : 0 ≤ |h|⁻¹ := inv_nonneg.mpr (abs_nonneg _)
      calc
        ‖Q h ω‖ =
            |h|⁻¹ * |w (x + X.X (Real.toNNReal h) ω) -
              w (x + X.X (Real.toNNReal h) ω - d * h)| := by
            simp [Q, Real.norm_eq_abs, abs_mul, abs_inv]
        _ ≤ |h|⁻¹ * (L * |d * h|) :=
            mul_le_mul_of_nonneg_left (by simpa only [hdif] using hk) hinv
        _ = L * |d| := by
          rw [abs_mul]
          field_simp [abs_ne_zero.mpr hh]
  have hpoint : ∀ᵐ ω ∂P, Tendsto (fun h : ℝ => Q h ω)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (d * deriv w x)) := by
    filter_upwards [] with ω
    exact avram_wave5_04c_original_C1_source_drift_pointwise X w hwC1 x d ω
  have hmain : Tendsto (fun h : ℝ => ∫ ω, Q h ω ∂P)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫ ω, d * deriv w x ∂P)) := by
    apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun _ : Ω => L * |d|)
    · exact Filter.Eventually.of_forall hmeas
    · exact Filter.Eventually.of_forall hbound
    · exact integrable_const _
    · exact hpoint
  simpa [Q] using hmain
