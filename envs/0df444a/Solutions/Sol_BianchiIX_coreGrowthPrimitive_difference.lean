-- Prove2me | solution 1 for BianchiIX.coreGrowthPrimitive_difference
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:34:48.170233+00:00
-- url     : https://prove2.me/submissions/c51e9535-9abc-4019-b846-42f6ce14cb06

import Definitions.Def_BianchiIX_Analysis_CoreGrowthBudget
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open BianchiIX

private theorem BianchiIX.core_log_bound {k : ℝ} (hk : 6 ≤ k) : Real.log (4 * k) ≤ k := by
  have hk0 : 0 ≤ k := by linarith
  apply (Real.log_le_iff_le_exp (by positivity : 0 < 4 * k)).mpr
  have H := Real.quadratic_le_exp_of_nonneg hk0
  nlinarith only [hk, H, sq_nonneg (k - 6)]

theorem solution {k a b : ℝ} (hk : 6 ≤ k)
    (ha : |a| ≤ Real.log (4 * k)) (hb : |b| ≤ Real.log (4 * k)) :
    coreGrowthPrimitive k b - coreGrowthPrimitive k a ≤ 2 * Real.pi + 48 / 10000 := by
  have hk0 : 0 < k := by linarith
  have hlen : b - a ≤ 2 * k := by
    have H := core_log_bound hk
    have Ha := (abs_le.mp ha).1
    have Hb := (abs_le.mp hb).2
    linarith only [H, Ha, Hb]
  have hlinear : 24 * ((1 / 10000) / k) * (b - a) ≤ 48 / 10000 := by
    calc
      _ ≤ 24 * ((1 / 10000) / k) * (2 * k) := mul_le_mul_of_nonneg_left hlen (by positivity)
      _ = 48 / 10000 := by field_simp; ring
  have hatan : 2 * (Real.arctan (Real.sinh b) - Real.arctan (Real.sinh a)) ≤ 2 * Real.pi := by
    linarith only [Real.arctan_lt_pi_div_two (Real.sinh b), Real.neg_pi_div_two_lt_arctan (Real.sinh a)]
  unfold coreGrowthPrimitive
  linarith only [hlinear, hatan]
