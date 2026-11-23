-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.log_nonexceptional_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:28.556098+00:00
-- url     : https://prove2.me/submissions/3d7505b3-11a8-4e8d-9495-4842df7890a8

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
private lemma log_exp_scale (ε x : ℝ) : Real.log (X1 ε x) = x ^ (ε / 5) := by unfold X1; exact Real.log_exp _
private lemma log_double_exp_scale (ε x : ℝ) : Real.log (X2 ε x) = x ^ (ε / 5) * Real.log x ^ 2 := by unfold X2; exact Real.log_exp _
private lemma exp_scale_rpow (ε x a : ℝ) : X1 ε x ^ a = Real.exp (x ^ (ε / 5) * a) := by unfold X1; rw [← Real.exp_mul]
private lemma double_exp_scale_rpow (ε x a : ℝ) : X2 ε x ^ a = Real.exp (x ^ (ε / 5) * Real.log x ^ 2 * a) := by unfold X2; rw [← Real.exp_mul]
end Formalism.HermitianLattices.ZeroFreeRegionGL2
end

set_option autoImplicit false
open Filter
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution : LogNE := by
  intro ε A hε hA
  have hε5 : 0 < ε / 5 := by positivity
  refine Filter.eventually_atTop.mp ?_
  filter_upwards [ev_log_pow A (ε / 5) hε5 1, ev_rpow_ge 3 (ε / 5) hε5, ev_log_ge 2,
    eventually_ge_atTop (1 : ℝ)] with x hAL hu3 hL hx1
  intro n q₁ d hn hnx hq1 hq1' hd hd'
  have hx0 : (0 : ℝ) < x := by linarith
  rw [pow_one] at hAL
  have hX1h : X1 ε x ^ (1 / 2 : ℝ) = Real.exp (x ^ (ε / 5) * (1 / 2)) := exp_scale_rpow ε x _
  have hX2h : X2 ε x ^ (1 / 2 : ℝ) = Real.exp (x ^ (ε / 5) * Real.log x ^ 2 * (1 / 2)) :=
    double_exp_scale_rpow ε x _
  have hX1p : 0 < X1 ε x ^ (1 / 2 : ℝ) := by rw [hX1h]; exact Real.exp_pos _
  have hX2p : 0 < X2 ε x ^ (1 / 2 : ℝ) := by rw [hX2h]; exact Real.exp_pos _
  have hq0 : (0 : ℝ) < q₁ := lt_trans hX1p hq1
  have hd0 : (0 : ℝ) < d := lt_trans hX2p hd
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : x ^ (ε / 5) / 2 < Real.log q₁ := by
    have := Real.log_lt_log hX1p hq1
    rw [hX1h, Real.log_exp] at this
    linarith
  have h2 : Real.log q₁ ≤ x ^ (ε / 5) := by
    have := Real.log_le_log hq0 hq1'
    rwa [log_exp_scale] at this
  have h3 : x ^ (ε / 5) * Real.log x ^ 2 / 2 < Real.log d := by
    have := Real.log_lt_log hX2p hd
    rw [hX2h, Real.log_exp] at this
    linarith
  have h4 : Real.log d ≤ x ^ (ε / 5) * Real.log x ^ 2 := by
    have := Real.log_le_log hd0 hd'
    rwa [log_double_exp_scale] at this
  have h5 : Real.log n ≤ A * Real.log x := by
    have := Real.log_le_log hn0 hnx
    rwa [Real.log_rpow hx0] at this
  refine ⟨h1, h2, h3, h4, ?_⟩
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    linarith
  have hL4 : (4 : ℝ) ≤ Real.log x ^ 2 := by nlinarith
  have hu0 : (0 : ℝ) ≤ x ^ (ε / 5) := by positivity
  have huL := mul_le_mul_of_nonneg_left hL4 hu0
  push_cast
  rw [Real.log_mul (mul_pos (mul_pos (show (0 : ℝ) < 4 by norm_num) hn0) hq0).ne' hd0.ne',
    Real.log_mul (mul_pos (show (0 : ℝ) < 4 by norm_num) hn0).ne' hq0.ne',
    Real.log_mul (show (4 : ℝ) ≠ 0 by norm_num) hn0.ne']
  nlinarith
end Formalism.HermitianLattices.ZeroFreeRegionGL2
