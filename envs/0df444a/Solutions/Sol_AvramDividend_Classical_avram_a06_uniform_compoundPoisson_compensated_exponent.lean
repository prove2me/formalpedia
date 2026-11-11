-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_uniform_compoundPoisson_compensated_exponent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T19:26:06.09344+00:00
-- url     : https://prove2.me/submissions/a1f75585-5ae8-455b-9b9f-89ef78faf650

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_negative_mark_restrict_identities
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

/-- Integrability permits actual compensator cancellation on the negative unit band. -/
theorem solution (θ : ℝ) (hθ : 0 ≤ θ) :
    θ + (∫ y in Ioo (-1 : ℝ) 0,
      (Real.exp (θ * y) - 1) ∂
        ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))) =
      laplaceExponent
        ((1 : ℝ) + (∫ y in Ioo (-1 : ℝ) 0,
          y ∂((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))))
        0 ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) θ := by
  let ν : Measure ℝ := (volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)
  have hrest :=
    AvramDividend.Classical.avram_a06_uniform_negative_mark_restrict_identities
  have hmass : ν Set.univ = 1 := by
    simp [ν, Measure.restrict_apply_univ, Real.volume_Ioo]
  haveI : IsFiniteMeasure ν := ⟨by simp [hmass]⟩
  have hY : Integrable (fun y : ℝ => y) ν := by
    refine (integrable_const (1 : ℝ)).mono measurable_id.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    have hb : |y| ≤ (1 : ℝ) := by
      apply abs_le.mpr
      constructor <;> linarith [hy.1, hy.2]
    simpa [Real.norm_eq_abs] using hb
  have hE : Integrable (fun y : ℝ => Real.exp (θ * y)) ν := by
    have hm : Measurable (fun y : ℝ => Real.exp (θ * y)) := by fun_prop
    refine (integrable_const (1 : ℝ)).mono hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    have hneg : θ * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθ hy.2.le
    have hb : Real.exp (θ * y) ≤ 1 := by
      simpa using (Real.exp_le_exp.mpr hneg)
    simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hb
  have hF : Integrable (fun y : ℝ => Real.exp (θ * y) - 1) ν :=
    hE.sub (integrable_const _)
  have hwide : ∀ᵐ y : ℝ ∂ν,
      (Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) y = 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    have hm : y ∈ Ioo (-1 : ℝ) 1 := ⟨hy.1, lt_trans hy.2 (by norm_num)⟩
    simp [Set.indicator_of_mem hm]
  have hkernel :
      (∫ y, (Real.exp (θ * y) - 1) - θ * y *
        (Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) y ∂ν) =
      (∫ y, (Real.exp (θ * y) - 1) - θ * y ∂ν) := by
    apply integral_congr_ae
    filter_upwards [hwide] with y hy
    rw [hy]
    ring
  have hcomp :
      θ + (∫ y, Real.exp (θ * y) - 1 ∂ν) =
      ((1 : ℝ) + (∫ y, y ∂ν)) * θ +
        (∫ y, (Real.exp (θ * y) - 1) - θ * y *
          (Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) y ∂ν) := by
    rw [hkernel, integral_sub hF (hY.const_mul θ), integral_const_mul]
    ring
  simpa [laplaceExponent, ν, hrest.1, hrest.2] using hcomp
