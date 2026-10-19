-- Prove2me | solution 1 for FickDiffusion.heatKernel_tendsto_initial
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:10:39.610399+00:00
-- url     : https://prove2.me/submissions/dad37a90-ace8-441a-bb0e-79e2a0f69da9

import Mathlib
import Definitions.Def_FickDiffusion_defs
open Real Filter Topology MeasureTheory FickDiffusion

namespace FickInit

/-- Change of variables: for `t > 0`, the convolution equals a Gaussian average. -/
lemma conv_eq (D : ℝ) (hD : 0 < D) (f : ℝ → ℝ) (x t : ℝ) (ht : 0 < t) :
    ∫ y, heatKernel D (x - y) t * f y =
      ∫ z, (1 / Real.sqrt π) * Real.exp (-z ^ 2) * f (x + Real.sqrt (4 * D * t) * z) := by
  set σ := Real.sqrt (4 * D * t) with hσ
  have hσ0 : 0 < σ := Real.sqrt_pos.mpr (by positivity)
  have hpi : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  set F : ℝ → ℝ := fun y => heatKernel D (x - y) t * f y with hF
  have h1 : ∫ z, F (x + σ * z) = σ⁻¹ * ∫ y, F y := by
    have := Measure.integral_comp_mul_left (fun y => F (x + y)) σ
    rw [this, abs_of_pos (inv_pos.mpr hσ0), smul_eq_mul, integral_add_left_eq_self]
  have h2 : ∫ y, F y = σ * ∫ z, F (x + σ * z) := by
    rw [h1]; field_simp
  rw [h2, ← integral_const_mul]
  congr 1
  funext z
  simp only [hF, heatKernel]
  have hsq : Real.sqrt (4 * π * D * t) = Real.sqrt π * σ := by
    rw [hσ, ← Real.sqrt_mul Real.pi_pos.le]; congr 1; ring
  have hσ2 : σ ^ 2 = 4 * D * t := Real.sq_sqrt (by positivity)
  rw [hsq, show x - (x + σ * z) = -(σ * z) by ring]
  have e : -(-(σ * z)) ^ 2 / (4 * D * t) = -z ^ 2 := by
    rw [neg_sq, mul_pow, hσ2]; field_simp
  rw [e]
  field_simp

end FickInit

open FickInit in
theorem solution (D : ℝ) (hD : 0 < D) (f : ℝ → ℝ) (hf : Continuous f)
    (hbdd : ∃ C, ∀ y, |f y| ≤ C) (x : ℝ) :
    Tendsto (fun t => ∫ y, heatKernel D (x - y) t * f y) (𝓝[>] 0) (𝓝 (f x)) := by
  obtain ⟨C, hC⟩ := hbdd
  have hpi : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  set h : ℝ → ℝ := fun z => (1 / Real.sqrt π) * Real.exp (-z ^ 2) with hh
  have hint : Integrable h := by
    have := (integrable_exp_neg_mul_sq (b := 1) (by norm_num)).const_mul (1 / Real.sqrt π)
    simpa [hh] using this
  have htot : ∫ z, h z = 1 := by
    simp only [hh]
    rw [integral_const_mul]
    have := integral_gaussian 1
    simp only [neg_mul, one_mul, div_one] at this
    rw [this]; field_simp
  -- the scale σ(t) tends to 0
  have hσ : Tendsto (fun t => Real.sqrt (4 * D * t)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t => Real.sqrt (4 * D * t)) (𝓝 0) (𝓝 (Real.sqrt (4 * D * 0))) :=
      Continuous.tendsto (by fun_prop) 0
    simp only [mul_zero, Real.sqrt_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hmain : Tendsto (fun t => ∫ z, h z * f (x + Real.sqrt (4 * D * t) * z)) (𝓝[>] 0)
      (𝓝 (∫ z, h z * f x)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun z => h z * C) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun t => (Continuous.aestronglyMeasurable (by
        simp only [hh]; fun_prop))
    · refine Eventually.of_forall fun t => Eventually.of_forall fun z => ?_
      rw [Real.norm_eq_abs, abs_mul]
      have hz : 0 ≤ h z := by simp only [hh]; positivity
      rw [abs_of_nonneg hz]
      exact mul_le_mul_of_nonneg_left (hC _) hz
    · exact hint.mul_const C
    · refine Eventually.of_forall fun z => ?_
      refine tendsto_const_nhds.mul ?_
      have : Tendsto (fun t => x + Real.sqrt (4 * D * t) * z) (𝓝[>] 0) (𝓝 (x + 0 * z)) :=
        tendsto_const_nhds.add (hσ.mul tendsto_const_nhds)
      rw [zero_mul, add_zero] at this
      exact (hf.tendsto x).comp this
  rw [integral_mul_const, htot, one_mul] at hmain
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [conv_eq D hD f x t ht]
