-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_source_scale_primitive_shifted_laplace_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:08:34.068436+00:00
-- url     : https://prove2.me/submissions/6b2e1cb2-cce7-4e9c-8c74-80df8ff87a12

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_source_scale_primitive_global_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_positive_laplace_interval_primitive_real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

/-- Negative spatial translates of the true source scale primitive are weighted L1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ y : ℝ) (hθ : 0 < θ) (hqθ : q < X.ψ θ) (hy : y ≤ 0) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) *
        (∫ t in (0 : ℝ)..(x + y), W t))
      (Ioi (0 : ℝ)) volume := by
  let U : ℝ → ℝ := fun z => ∫ t in (0 : ℝ)..z, W t
  have hUmono : Monotone U :=
    avram_wave4_p2_source_scale_primitive_global_monotone X q W hW
  have hUnonneg (z : ℝ) : 0 ≤ U z := by
    by_cases hz : z ≤ 0
    · change 0 ≤ ∫ t in (0 : ℝ)..z, W t
      rw [avram_wave4_p2_scale_primitive_zero_nonpositive X q W hW z hz]
    · have hz0 : 0 ≤ z := le_of_lt (lt_of_not_ge hz)
      change 0 ≤ ∫ t in (0 : ℝ)..z, W t
      exact intervalIntegral.integral_nonneg hz0 (fun t ht => hW.2.1 t ht.1)
  have hUmeas : Measurable U := hUmono.measurable
  have hmeas : Measurable (fun x : ℝ => Real.exp (-(θ * x)) * U (x + y)) := by
    fun_prop
  have hbase : IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * U x)
      (Ioi (0 : ℝ)) volume :=
    (positive_laplace_interval_primitive_real W θ hθ
      (hW.2.2.2.2 θ hθ.le hqθ).1).1
  have hle (x : ℝ) : Real.exp (-(θ * x)) * U (x + y) ≤
      Real.exp (-(θ * x)) * U x := by
    apply mul_le_mul_of_nonneg_left
    · exact hUmono (by linarith)
    · exact Real.exp_nonneg _
  have hnorm (x : ℝ) : ‖Real.exp (-(θ * x)) * U (x+y)‖ ≤
      Real.exp (-(θ * x)) * U x := by
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (hUnonneg (x+y)))]
    exact hle x
  change IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * U (x + y))
    (Ioi (0 : ℝ)) volume
  exact hbase.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hnorm)
