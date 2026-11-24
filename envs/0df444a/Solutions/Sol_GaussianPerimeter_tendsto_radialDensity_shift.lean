-- Prove2me | solution 1 for GaussianPerimeter.tendsto_radialDensity_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:23:54.446679+00:00
-- url     : https://prove2.me/submissions/8714edec-9ce0-492a-b699-0a6ae7faf5e2

module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_GaussianPerimeter_Radial
section
public section
open Filter MeasureTheory Set
open scoped Topology
namespace GaussianPerimeter
private theorem abs_log_remainder {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |Real.log (1 + u) - u + u ^ 2 / 2| ≤ 2 * |u| ^ 3 := by
  have hu' : |-u| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hu' 2
  rw [abs_neg] at h
  calc
    |Real.log (1 + u) - u + u ^ 2 / 2| ≤ |u| ^ 3 / (1 - |u|) := by
      convert h using 2
      simp [Finset.sum_range_succ]
      ring
    _ ≤ 2 * |u| ^ 3 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_nonneg (pow_nonneg (abs_nonneg u) 3)
        (show 0 ≤ 1 - 2 * |u| by linarith)]
private theorem profileExponent_error {t w : ℝ} (ht : 0 < t) (hw : |w / t| ≤ 1 / 2) :
    |profileExponent t w - (-w ^ 2)| ≤ 2 * |w| ^ 3 / t := by
  have h₁ : profileExponent t w - (-w ^ 2) =
      t ^ 2 * (Real.log (1 + w / t) - w / t + (w / t) ^ 2 / 2) := by
    unfold profileExponent
    field_simp
    ring
  rw [h₁, abs_mul, abs_of_nonneg (sq_nonneg _)]
  calc
    t ^ 2 * |Real.log (1 + w / t) - w / t + (w / t) ^ 2 / 2| ≤
        t ^ 2 * (2 * |w / t| ^ 3) :=
      mul_le_mul_of_nonneg_left (abs_log_remainder hw) (sq_nonneg _)
    _ = 2 * |w| ^ 3 / t := by
      rw [abs_div, abs_of_pos ht]
      field_simp
private theorem radialMode_atTop : Tendsto radialMode atTop atTop := by
  apply Real.tendsto_sqrt_atTop.comp
  exact tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1)
private theorem eventually_mode_pos : ∀ᶠ n in atTop, 0 < radialMode n :=
  radialMode_atTop.eventually_gt_atTop 0
private theorem profile_tendsto (w : ℝ) :
    Tendsto (fun n => radialProfile n w) atTop (𝓝 (Real.exp (-w ^ 2))) := by
  have hu : Tendsto (fun n => w / radialMode n) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_inv_atTop_zero.comp radialMode_atTop).const_mul w
  have hwsmall : ∀ᶠ n in atTop, |w / radialMode n| < 1 / 2 := by
    exact hu.abs.eventually (gt_mem_nhds (by norm_num : |(0 : ℝ)| < 1 / 2))
  have hbound : Tendsto (fun n => 2 * |w| ^ 3 / radialMode n) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_inv_atTop_zero.comp radialMode_atTop).const_mul (2 * |w| ^ 3)
  have hExp : Tendsto (fun n => profileExponent (radialMode n) w) atTop (𝓝 (-w ^ 2)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hbound
    filter_upwards [eventually_mode_pos, hwsmall] with n hn hsmall
    simpa [Real.dist_eq] using profileExponent_error hn hsmall.le
  apply (Real.continuous_exp.continuousAt.tendsto.comp hExp).congr'
  filter_upwards [radialMode_atTop.eventually_gt_atTop (-w)] with n hn
  have h : 0 < radialMode n + w := by linarith
  simp [radialProfile, h]
private theorem profile_nonneg (n : ℕ) (w : ℝ) : 0 ≤ radialProfile n w := by
  unfold radialProfile
  split <;> positivity
private theorem profile_le (n : ℕ) (hn : 0 < radialMode n) (w : ℝ) :
    radialProfile n w ≤ Real.exp (-(1 / 2) * w ^ 2) := by
  unfold radialProfile
  split_ifs with h
  · apply Real.exp_le_exp.mpr
    have hu : 0 < 1 + w / radialMode n := by
      rw [add_div_eq_mul_add_div _ _ hn.ne', one_mul]
      exact div_pos h hn
    have hlog := Real.log_le_sub_one_of_pos hu
    have hb := mul_le_mul_of_nonneg_left hlog (sq_nonneg (radialMode n))
    have heq : radialMode n ^ 2 * (1 + w / radialMode n - 1) = radialMode n * w := by
      field_simp
      ring
    rw [heq] at hb
    unfold profileExponent
    linarith
  · positivity
private theorem profile_measurable (n : ℕ) : Measurable (radialProfile n) := by
  unfold radialProfile profileExponent
  apply Measurable.ite
  · exact measurableSet_lt measurable_const (by fun_prop)
  · fun_prop
  · exact measurable_const
private theorem profile_integral_tendsto :
    Tendsto (fun n => ∫ w : ℝ, radialProfile n w) atTop (𝓝 (Real.sqrt Real.pi)) := by
  have hGaussian : (∫ w : ℝ, Real.exp (-w ^ 2)) = Real.sqrt Real.pi := by
    simpa using integral_gaussian 1
  rw [← hGaussian]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun w : ℝ => Real.exp (-(1 / 2) * w ^ 2)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun n => (profile_measurable n).aestronglyMeasurable
  · filter_upwards [eventually_mode_pos] with n hn
    exact ae_of_all _ fun w => by
      rw [Real.norm_of_nonneg (profile_nonneg n w)]
      exact profile_le n hn w
  · exact integrable_exp_neg_mul_sq (by norm_num)
  · exact ae_of_all _ profile_tendsto
private theorem kernel_shift (n : ℕ) (hn : 0 < radialMode n) (w : ℝ) :
    radialKernel n (radialMode n + w) =
      (radialMode n ^ (n - 1) * Real.exp (-(radialMode n) ^ 2 / 2)) * radialProfile n w := by
  let t := radialMode n
  change 0 < t at hn
  have hsq : t ^ 2 = ((n - 1 : ℕ) : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  unfold radialKernel radialProfile profileExponent
  change (Ioi (0 : ℝ)).indicator _ (t + w) =
    (t ^ (n - 1) * Real.exp (-t ^ 2 / 2)) *
      (if 0 < t + w then Real.exp (t ^ 2 * Real.log (1 + w / t) - t * w - w ^ 2 / 2) else 0)
  by_cases hp : 0 < t + w
  · rw [if_pos hp, indicator_of_mem (show t + w ∈ Ioi (0 : ℝ) from hp)]
    have hu : 0 < 1 + w / t := by
      have hEq : 1 + w / t = (t + w) / t := by field_simp
      rw [hEq]
      exact div_pos hp hn
    rw [show t ^ 2 * Real.log (1 + w / t) - t * w - w ^ 2 / 2 =
      t ^ 2 * Real.log (1 + w / t) + (-(t + w) ^ 2 / 2 - (-t ^ 2 / 2)) by ring,
      Real.exp_add, Real.exp_sub, hsq, Real.exp_nat_mul, Real.exp_log hu]
    have heq : t * (1 + w / t) = t + w := by field_simp
    rw [← heq, mul_pow]
    field_simp [Real.exp_ne_zero]
  · rw [if_neg hp, indicator_of_notMem (show t + w ∉ Ioi (0 : ℝ) from hp), mul_zero]
private theorem density_shift_eq (n : ℕ) (hn : 0 < radialMode n) (w : ℝ) :
    radialDensity n (radialMode n + w) = radialProfile n w / (∫ t : ℝ, radialProfile n t) := by
  unfold radialDensity
  have hShift : (∫ t : ℝ, radialKernel n t) =
      ∫ t : ℝ, radialKernel n (radialMode n + t) := by
    exact (integral_add_left_eq_self _ _).symm
  rw [hShift]
  simp_rw [kernel_shift n hn]
  rw [integral_const_mul]
  exact mul_div_mul_left _ _ (by positivity)
end GaussianPerimeter
end
end

set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory Set
open scoped Topology
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution (w : ℝ) :
    Tendsto (fun n => radialDensity n (Real.sqrt ((n - 1 : ℕ) : ℝ) + w))
      atTop (𝓝 (Real.exp (-w ^ 2) / Real.sqrt Real.pi)) := by
  apply ((profile_tendsto w).div profile_integral_tendsto (by positivity)).congr'
  filter_upwards [eventually_mode_pos] with n hn
  exact (density_shift_eq n hn w).symm
end GaussianPerimeter
