-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.numerical_zero_density_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:55.397891+00:00
-- url     : https://prove2.me/submissions/f24cb0b8-b62a-493b-a571-bd3ac074da5a

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_WeightedVonMangoldtSumIdentity
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_NumericalZeroDensityBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Filter
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
private lemma ev_log_pow (K a : ℝ) (ha : 0 < a) (k : ℕ) :
    ∀ᶠ x : ℝ in atTop, K * Real.log x ^ k ≤ x ^ a := by
  have h1 : Asymptotics.IsLittleO atTop (fun x : ℝ => K * Real.log x ^ (k : ℝ)) (fun x => x ^ a) :=
    (isLittleO_log_rpow_rpow_atTop (k : ℝ) ha).const_mul_left K
  filter_upwards [h1.bound one_pos, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  rw [Real.rpow_natCast, one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hx0 a)] at hx
  exact le_trans (le_abs_self _) hx
private lemma ev_rpow_ge (K a : ℝ) (ha : 0 < a) : ∀ᶠ x : ℝ in atTop, K ≤ x ^ a := (tendsto_rpow_atTop ha).eventually_ge_atTop K
private lemma ev_log_ge (K : ℝ) : ∀ᶠ x : ℝ in atTop, K ≤ Real.log x := Real.tendsto_log_atTop.eventually_ge_atTop K
private lemma log_eight_le_seven : Real.log 8 ≤ 7 := by
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 by norm_num)
  linarith
private lemma log_eight_nonneg : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
private lemma exp_scale_pos (ε x : ℝ) : 0 < X1 ε x := by unfold X1; exact Real.exp_pos _
private lemma double_exp_scale_pos (ε x : ℝ) : 0 < X2 ε x := by unfold X2; exact Real.exp_pos _
private lemma log_exp_scale (ε x : ℝ) : Real.log (X1 ε x) = x ^ (ε / 5) := by unfold X1; exact Real.log_exp _
private lemma log_double_exp_scale (ε x : ℝ) : Real.log (X2 ε x) = x ^ (ε / 5) * Real.log x ^ 2 := by unfold X2; exact Real.log_exp _
private lemma double_exp_scale_rpow (ε x a : ℝ) : X2 ε x ^ a = Real.exp (x ^ (ε / 5) * Real.log x ^ 2 * a) := by unfold X2; rw [← Real.exp_mul]
private lemma log_8X1X2 (ε x : ℝ) :
    Real.log (8 * X1 ε x * X2 ε x) = Real.log 8 + x ^ (ε / 5) + x ^ (ε / 5) * Real.log x ^ 2 := by
  rw [Real.log_mul (mul_pos (by norm_num) (exp_scale_pos ε x)).ne' (double_exp_scale_pos ε x).ne',
    Real.log_mul (by norm_num) (exp_scale_pos ε x).ne', log_exp_scale, log_double_exp_scale]
end Formalism.HermitianLattices.ZeroFreeRegionGL2
end

set_option autoImplicit false
open Filter
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution : IncrementSizeConditions := by
  intro ε C hε hε1 hC
  have hε5 : 0 < ε / 5 := by positivity
  have hε20 : 0 < ε / 20 := by positivity
  refine Filter.eventually_atTop.mp ?_
  filter_upwards [ev_log_ge 5, ev_rpow_ge 16 (ε / 5) hε5,
    ev_rpow_ge (|Real.log (8 * C)| + 2) (ε / 5) hε5, ev_log_pow 3 (ε / 20) hε20 2,
    ev_rpow_ge 2 (1 / 2) (by norm_num), eventually_ge_atTop (1 : ℝ)] with x hL hu16 huC hv hs hx1
  have hx0 : (0 : ℝ) < x := by linarith
  have hl8 := log_eight_le_seven
  have hl80 := log_eight_nonneg
  have hu0 : 0 < x ^ (ε / 5) := by positivity
  have he : x ^ (ε / 6) ≤ x ^ (ε / 5) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hL2 : 25 ≤ Real.log x ^ 2 := by nlinarith
  have huL := mul_le_mul_of_nonneg_left hL2 hu0.le
  have h8 : 8 * X1 ε x * X2 ε x =
      Real.exp (Real.log 8 + x ^ (ε / 5) + x ^ (ε / 5) * Real.log x ^ 2) := by
    unfold X1 X2
    rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 8)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m₀ hm0 hm
    have h16 : Real.log 16 ≤ 15 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 16 by norm_num)
      linarith
    have hlm : Real.log m₀ ≤ Real.log 16 + 3 * x ^ (ε / 5) := by
      have := Real.log_le_log hm0 hm
      rwa [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at this
    rw [log_double_exp_scale]
    nlinarith [mul_le_mul_of_nonneg_left hlm (sq_nonneg (Real.log x)),
      mul_nonneg (sq_nonneg (Real.log x)) (by linarith : (0 : ℝ) ≤ x ^ (ε / 5) - Real.log 16)]
  · rw [log_double_exp_scale]
    nlinarith
  · rw [h8, ← Real.exp_mul, double_exp_scale_rpow]
    apply Real.exp_le_exp.mpr
    nlinarith
  · rw [log_8X1X2]
    nlinarith [mul_nonneg hu0.le (sq_nonneg (Real.log x))]
  · rw [log_8X1X2]
    have hsp : x ^ (ε / 4) = x ^ (ε / 5) * x ^ (ε / 20) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    rw [hsp]
    nlinarith [mul_le_mul_of_nonneg_left hv hu0.le]
  · have hE : 8 * C * Real.exp ((Real.log 8 + x ^ (ε / 5) + x ^ (ε / 5) * Real.log x ^ 2) * (1 / 4)) =
        Real.exp (Real.log (8 * C) +
          (Real.log 8 + x ^ (ε / 5) + x ^ (ε / 5) * Real.log x ^ 2) * (1 / 4)) := by
      rw [Real.exp_add, Real.exp_log (mul_pos (by norm_num) hC)]
    have hle : Real.exp (Real.log (8 * C) +
          (Real.log 8 + x ^ (ε / 5) + x ^ (ε / 5) * Real.log x ^ 2) * (1 / 4)) ≤
        Real.exp (x ^ (ε / 5) * Real.log x ^ 2 * (9 / 10)) := by
      apply Real.exp_le_exp.mpr
      have := le_abs_self (Real.log (8 * C))
      nlinarith
    rw [h8, ← Real.exp_mul, double_exp_scale_rpow]
    linarith
  · rw [Real.rpow_add hx0]
    have hwp : 0 < x ^ ε := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hs hwp.le]
end Formalism.HermitianLattices.ZeroFreeRegionGL2
