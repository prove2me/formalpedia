-- Prove2me | solution 1 for FickDiffusion.heatKernel_fundamental_solution
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:18:50.739995+00:00
-- url     : https://prove2.me/submissions/7b2c575a-ed17-4805-9a7d-cb25f74a5f2e

import Mathlib
import Definitions.Def_FickDiffusion_defs
open Real Filter Topology MeasureTheory FickDiffusion

theorem fick_pde (D : ℝ) (hD : 0 < D) (x t : ℝ) (ht : 0 < t) :
    deriv (fun s => heatKernel D x s) t =
      D * deriv (fun y => deriv (fun z => heatKernel D z t) y) x := by
  have hc : 0 < 4 * D * t := by positivity
  have hq : 0 < 4 * π * D * t := by positivity
  set A := 1 / Real.sqrt (4 * π * D * t) with hA
  -- first space derivative
  have hd1 : ∀ y : ℝ, HasDerivAt (fun z => heatKernel D z t)
      (A * (Real.exp (-y ^ 2 / (4 * D * t)) * (-(2 * y) / (4 * D * t)))) y := by
    intro y
    have h1 : HasDerivAt (fun z : ℝ => -z ^ 2 / (4 * D * t)) (-(2 * y) / (4 * D * t)) y := by
      have := ((hasDerivAt_pow 2 y).neg).div_const (4 * D * t)
      exact this.congr_deriv (by norm_num <;> ring)
    exact (h1.exp).const_mul A
  have hderiv1 : deriv (fun z => heatKernel D z t) =
      fun y => A * (Real.exp (-y ^ 2 / (4 * D * t)) * (-(2 * y) / (4 * D * t))) :=
    funext fun y => (hd1 y).deriv
  -- second space derivative
  have hd2 : HasDerivAt (fun y => A * (Real.exp (-y ^ 2 / (4 * D * t)) * (-(2 * y) / (4 * D * t))))
      (A * (Real.exp (-x ^ 2 / (4 * D * t)) * (-(2 * x) / (4 * D * t)) * (-(2 * x) / (4 * D * t))
        + Real.exp (-x ^ 2 / (4 * D * t)) * (-2 / (4 * D * t)))) x := by
    have h1 : HasDerivAt (fun z : ℝ => -z ^ 2 / (4 * D * t)) (-(2 * x) / (4 * D * t)) x := by
      have := ((hasDerivAt_pow 2 x).neg).div_const (4 * D * t)
      exact this.congr_deriv (by norm_num <;> ring)
    have h2 : HasDerivAt (fun z : ℝ => -(2 * z) / (4 * D * t)) (-2 / (4 * D * t)) x := by
      have := (((hasDerivAt_id' x).const_mul 2).neg).div_const (4 * D * t)
      exact this.congr_deriv (by norm_num <;> ring)
    exact ((h1.exp).mul h2).const_mul A
  rw [hderiv1, hd2.deriv]
  -- time derivative
  have ht1 : HasDerivAt (fun s => Real.sqrt (4 * π * D * s))
      (4 * π * D / (2 * Real.sqrt (4 * π * D * t))) t := by
    have := ((hasDerivAt_id' t).const_mul (4 * π * D)).sqrt (by positivity)
    exact this.congr_deriv (by norm_num <;> ring)
  have ht2 : HasDerivAt (fun s => 1 / Real.sqrt (4 * π * D * s))
      (-(4 * π * D / (2 * Real.sqrt (4 * π * D * t))) / Real.sqrt (4 * π * D * t) ^ 2) t := by
    have := (hasDerivAt_const t (1 : ℝ)).div ht1 (Real.sqrt_pos.mpr hq).ne'
    exact this.congr_deriv (by norm_num <;> ring)
  have ht3 : HasDerivAt (fun s => -x ^ 2 / (4 * D * s)) (x ^ 2 * (4 * D) / (4 * D * t) ^ 2) t := by
    have := (hasDerivAt_const t (-x ^ 2)).div ((hasDerivAt_id' t).const_mul (4 * D)) (by positivity)
    exact this.congr_deriv (by norm_num <;> ring)
  have ht4 : HasDerivAt (fun s => 1 / Real.sqrt (4 * π * D * s) * Real.exp (-x ^ 2 / (4 * D * s)))
      (-(4 * π * D / (2 * Real.sqrt (4 * π * D * t))) / Real.sqrt (4 * π * D * t) ^ 2 *
        Real.exp (-x ^ 2 / (4 * D * t)) + 1 / Real.sqrt (4 * π * D * t) *
        (Real.exp (-x ^ 2 / (4 * D * t)) * (x ^ 2 * (4 * D) / (4 * D * t) ^ 2))) t :=
    ht2.mul (ht3.exp)
  have hfun : (fun s => heatKernel D x s) =
      fun s => 1 / Real.sqrt (4 * π * D * s) * Real.exp (-x ^ 2 / (4 * D * s)) := rfl
  rw [hfun, ht4.deriv]
  have hs : Real.sqrt (4 * π * D * t) ^ 2 = 4 * π * D * t := Real.sq_sqrt hq.le
  have hs0 : Real.sqrt (4 * π * D * t) ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  rw [hA, hs]
  field_simp
  ring

theorem fick_mass (D : ℝ) (hD : 0 < D) (t : ℝ) (ht : 0 < t) :
    ∫ x, heatKernel D x t = 1 := by
  unfold heatKernel
  rw [integral_const_mul]
  have hb : 0 < 1 / (4 * D * t) := by positivity
  have h := integral_gaussian (1 / (4 * D * t))
  have e : (fun x : ℝ => Real.exp (-x ^ 2 / (4 * D * t))) =
      fun x => Real.exp (-(1 / (4 * D * t)) * x ^ 2) := by
    funext x; congr 1; ring
  rw [e, h]
  have hpos : 0 < 4 * π * D * t := by positivity
  rw [show π / (1 / (4 * D * t)) = 4 * π * D * t by field_simp]
  rw [one_div_mul_cancel (Real.sqrt_pos.mpr hpos).ne']

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
theorem fick_init (D : ℝ) (hD : 0 < D) (f : ℝ → ℝ) (hf : Continuous f)
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


theorem solution (D : ℝ) (hD : 0 < D) :
    (∀ x t : ℝ, 0 < t → deriv (fun s => heatKernel D x s) t =
        D * deriv (fun y => deriv (fun z => heatKernel D z t) y) x) ∧
    (∀ t : ℝ, 0 < t → ∫ x, heatKernel D x t = 1) ∧
    (∀ f : ℝ → ℝ, Continuous f → (∃ C, ∀ y, |f y| ≤ C) → ∀ x : ℝ,
        Tendsto (fun t => ∫ y, heatKernel D (x - y) t * f y) (𝓝[>] 0) (𝓝 (f x))) :=
  ⟨fun x t ht => fick_pde D hD x t ht, fun t ht => fick_mass D hD t ht,
    fun f hf hb x => fick_init D hD f hf hb x⟩
