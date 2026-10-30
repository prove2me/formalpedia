-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_original_supremum_scale_clock_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:24:44.221111+00:00
-- url     : https://prove2.me/submissions/9d688963-667f-4b98-9433-e557e6282e62

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_levy_positive_root_true_exp_clock_supremum_full_law_ws01d
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_lintegral
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Under the original Exp(R) observation law the scale reward of the true
supremum has the exact exponential-root moment, including BV W(0)>0. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q R φ : ℝ) (hR : 0 < R) (hqR : q < R)
    (hφ : 0 < φ) (hroot : X.ψ φ = R)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    (∫⁻ z : Ω × ℝ,
      ENNReal.ofReal (W (runningSup X z.2.toNNReal z.1))
      ∂(P.prod (expMeasure R))) =
    ENNReal.ofReal (φ / (R - q)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  letI : IsProbabilityMeasure (expMeasure R) :=
    isProbabilityMeasure_expMeasure hR
  let S : Ω × ℝ → ℝ := fun z =>
    runningSup X z.2.toNNReal z.1
  have hS : Measurable S :=
    (levy_exponential_real_clock_extrema_drawdown_measurable X).fst.fst
  have hMeasW : Measurable W :=
    (scaleFunction_monotone X q W hW).measurable
  have hSup :=
    levy_positive_root_true_exp_clock_supremum_full_law_ws01d
      X R hR φ hφ hroot
  have hLap := scaleFunction_tilted_positive_lintegral
    X q W hW 0 φ (by positivity) (by rw [zero_add, hroot]; exact hqR)
  simp only [neg_zero, zero_mul, Real.exp_zero, one_mul,
    zero_add, neg_mul] at hLap
  have hPDF : ∀ y : ℝ,
      exponentialPDF φ y =
      if 0 ≤ y then ENNReal.ofReal φ *
        ENNReal.ofReal (Real.exp (-(φ * y))) else 0 := by
    intro y
    by_cases hy : 0 ≤ y
    · rw [exponentialPDF_of_nonneg hy, if_pos hy]
      rw [ENNReal.ofReal_mul hφ.le]
    · rw [exponentialPDF_of_neg (lt_of_not_ge hy), if_neg hy]
  have hDens : (∫⁻ y : ℝ,
      ENNReal.ofReal (W y) ∂(expMeasure φ)) =
      ENNReal.ofReal φ * (∫⁻ y : ℝ in Ioi 0,
        ENNReal.ofReal (Real.exp (-(φ * y)) * W y)) := by
    change (∫⁻ y : ℝ,
      ENNReal.ofReal (W y) ∂(volume.withDensity (exponentialPDF φ))) = _
    have hDensity :
        (∫⁻ y : ℝ, ENNReal.ofReal (W y)
          ∂(volume.withDensity (exponentialPDF φ))) =
        (∫⁻ y : ℝ, exponentialPDF φ y * ENNReal.ofReal (W y)
          ∂volume) := by
      exact lintegral_withDensity_eq_lintegral_mul _
        (measurable_exponentialPDFReal φ).ennreal_ofReal
        hMeasW.ennreal_ofReal
    rw [hDensity]
    have hMeasF : Measurable (fun y : ℝ =>
        ENNReal.ofReal (Real.exp (-(φ * y)) * W y)) :=
      ((Real.measurable_exp.comp
        (measurable_const.mul measurable_id).neg).mul hMeasW).ennreal_ofReal
    rw [← lintegral_const_mul (μ := volume.restrict (Ioi (0 : ℝ)))
      (ENNReal.ofReal φ) hMeasF]
    rw [← lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr_ae
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with y hy
    by_cases hpos : 0 < y
    · rw [hPDF y, if_pos hpos.le]
      simp only [Set.indicator, Set.mem_Ioi, if_pos hpos]
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
      ring
    · have hneg : y < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hy
      simp [hPDF y, not_le.mpr hneg, Set.indicator_of_notMem
        (show y ∉ Ioi (0 : ℝ) by simpa using not_lt.mpr hneg.le)]
  calc
    _ = ∫⁻ y : ℝ, ENNReal.ofReal (W y)
         ∂(Measure.map S (P.prod (expMeasure R))) := by
           simpa only [S] using
             (lintegral_map hMeasW.ennreal_ofReal hS).symm
    _ = ∫⁻ y : ℝ, ENNReal.ofReal (W y)
         ∂(expMeasure φ) := by rw [hSup]
    _ = ENNReal.ofReal φ *
      ENNReal.ofReal ((X.ψ φ - q)⁻¹) := by rw [hDens, hLap]
    _ = ENNReal.ofReal (φ / (R - q)) := by
      rw [hroot, div_eq_mul_inv, ENNReal.ofReal_mul hφ.le]
