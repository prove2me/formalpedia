-- Prove2me | solution 1 for BookProof.QgHermiteCore.tendsto_exp_abs_mul_gaussH_atTop
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:23:19.083657+00:00
-- url     : https://prove2.me/submissions/cd2bd320-a61f-41b0-bab9-f58bde8ba79c

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
open Filter Topology
set_option autoImplicit false

theorem solution (c : ℝ) :
    Tendsto (fun x : ℝ => Real.exp (c * |x|) * Real.exp (-x ^ 2 / 4)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun x : ℝ => x ^ 2 / 8) atTop atTop :=
    (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).atTop_div_const (by norm_num)
  have hlim : Tendsto (fun x : ℝ => Real.exp (2 * c ^ 2) * Real.exp (-x ^ 2 / 8))
      atTop (𝓝 0) := by
    have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hpow).const_mul (Real.exp (2 * c ^ 2))
    simpa only [Function.comp_def, neg_div, mul_zero] using h
  apply squeeze_zero (fun x => by positivity) (fun x => ?_) hlim
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (|x| - 4 * c), sq_abs x]
#print axioms solution
