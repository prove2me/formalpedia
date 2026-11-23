-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.numerical_bound_unit_modulus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:47.671795+00:00
-- url     : https://prove2.me/submissions/c8006abc-066f-4f9b-ab3c-a3babe41da00

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
private lemma log_exp_scale (ε x : ℝ) : Real.log (X1 ε x) = x ^ (ε / 5) := by unfold X1; exact Real.log_exp _
private lemma exp_scale_rpow (ε x a : ℝ) : X1 ε x ^ a = Real.exp (x ^ (ε / 5) * a) := by unfold X1; rw [← Real.exp_mul]
private lemma log_8X1 (ε x : ℝ) : Real.log (8 * X1 ε x) = Real.log 8 + x ^ (ε / 5) := by
  rw [Real.log_mul (by norm_num) (exp_scale_pos ε x).ne', log_exp_scale]
end Formalism.HermitianLattices.ZeroFreeRegionGL2
end

set_option autoImplicit false
open Filter
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution : UnitModulusIncrementConditions := by
  intro ε C hε hε1 hC
  have hε5 : 0 < ε / 5 := by positivity
  have hε20 : 0 < ε / 20 := by positivity
  refine Filter.eventually_atTop.mp ?_
  filter_upwards [ev_log_pow 801 (ε / 5) hε5 1, ev_log_pow 807 (ε / 5) hε5 3, ev_log_ge 1,
    ev_rpow_ge 7 (ε / 5) hε5, ev_rpow_ge ((20 / 13) * (|Real.log (4 * C)| + 2)) (ε / 5) hε5,
    ev_rpow_ge 2 (ε / 20) hε20, ev_log_pow (4 * C) ε hε 1, ev_rpow_ge 8 ε hε,
    eventually_ge_atTop (1 : ℝ)] with x hA hB hL hu7 huC hv hw hw8 hx1
  have hx0 : (0 : ℝ) < x := by linarith
  rw [pow_one] at hA hw
  have hl8 := log_eight_le_seven
  have hl80 := log_eight_nonneg
  have hLp : 0 < Real.log x := by linarith
  have hL3 : 0 < Real.log x ^ 3 := pow_pos hLp 3
  have hsq7 := mul_nonneg (sq_nonneg (Real.log x)) (sub_nonneg.mpr hl8)
  have hsqL := mul_nonneg (sq_nonneg (Real.log x)) (sub_nonneg.mpr hL)
  have hwp : 0 < x ^ ε := by positivity
  refine ⟨?_, by linarith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have e : Real.exp (((400 : ℕ) : ℝ) * Real.log x) = x ^ 400 := by
      rw [Real.exp_nat_mul, Real.exp_log hx0]
    rw [← e, exp_scale_rpow]
    apply Real.exp_lt_exp.mpr
    push_cast
    linarith
  · rw [log_exp_scale]
    nlinarith
  · have hlog : Real.log (8 * (x ^ 400) ^ 2) = Real.log 8 + 800 * Real.log x := by
      rw [Real.log_mul (by norm_num) (pow_pos (pow_pos hx0 400) 2).ne', Real.log_pow, Real.log_pow]
      push_cast
      ring
    rw [log_exp_scale, hlog]
    nlinarith
  · rw [log_exp_scale]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  · rw [log_8X1]
    have := Real.rpow_le_rpow_of_exponent_le hx1 (show ε / 6 ≤ ε / 5 by linarith)
    linarith
  · rw [log_8X1]
    have hsp : x ^ (ε / 4) = x ^ (ε / 5) * x ^ (ε / 20) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    rw [hsp]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x ^ (ε / 5)) (by linarith : (0 : ℝ) ≤ x ^ (ε / 20) - 2)]
  · have hsplit : x ^ (1 / 2 + ε) = x ^ (1 / 2 : ℝ) * x ^ ε := Real.rpow_add hx0 _ _
    have hs2 : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num
    have hden : (x ^ (1 / 2 + ε) / 2) ^ 2 = x * (x ^ ε) ^ 2 / 4 := by
      rw [hsplit, div_pow, mul_pow, hs2]
      ring
    rw [hden, Real.rpow_neg hx0.le, div_le_iff₀ (by positivity)]
    have hwne : x ^ ε ≠ 0 := hwp.ne'
    have hr : (x ^ ε)⁻¹ * (x * (x ^ ε) ^ 2 / 4) = x * x ^ ε / 4 := by
      field_simp
    rw [hr]
    nlinarith [mul_le_mul_of_nonneg_left hw hx0.le]
  · rw [Real.rpow_neg hx0.le, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hw8
  · have h8X : 8 * X1 ε x = Real.exp (Real.log 8 + x ^ (ε / 5)) := by
      unfold X1
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 8)]
    have hE : 4 * C * Real.exp ((Real.log 8 + x ^ (ε / 5)) * (1 / 4)) =
        Real.exp (Real.log (4 * C) + (Real.log 8 + x ^ (ε / 5)) * (1 / 4)) := by
      rw [Real.exp_add, Real.exp_log (mul_pos (by norm_num) hC)]
    have hle : Real.exp (Real.log (4 * C) + (Real.log 8 + x ^ (ε / 5)) * (1 / 4)) ≤
        Real.exp (x ^ (ε / 5) * (9 / 10)) := by
      apply Real.exp_le_exp.mpr
      have := le_abs_self (Real.log (4 * C))
      linarith
    rw [h8X, ← Real.exp_mul, exp_scale_rpow]
    linarith
end Formalism.HermitianLattices.ZeroFreeRegionGL2
