-- Prove2me | solution 1 for BianchiIX.core_log_quotient_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:27:22.943526+00:00
-- url     : https://prove2.me/submissions/60a8d933-18ab-41df-b551-f749233ec8e2

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX


theorem solution {d x y A B : ℝ} (hd : 999 / 1000 ≤ d)
    (hx : |x| ≤ A) (hy : |y| ≤ B) : |x / d - y / d ^ 2| ≤ 11 / 10 * (A + B) := by
  have hd0 : 0 < d := by linarith only [hd]
  have hA : 0 ≤ A := (abs_nonneg _).trans hx
  have hB : 0 ≤ B := (abs_nonneg _).trans hy
  have hdx : |x / d| ≤ 11 / 10 * A := by
    rw [abs_div, abs_of_pos hd0, div_le_iff₀ hd0]
    nlinarith only [hx, mul_nonneg hA (show 0 ≤ d - 10 / 11 by linarith only [hd])]
  have hdy : |y / d ^ 2| ≤ 11 / 10 * B := by
    rw [abs_div, abs_pow, abs_of_pos hd0, div_le_iff₀ (sq_pos_of_pos hd0)]
    have hsq : 10 / 11 ≤ d ^ 2 := by nlinarith only [hd]
    nlinarith only [hy, mul_nonneg hB (sub_nonneg.mpr hsq)]
  exact (abs_sub _ _).trans ((add_le_add hdx hdy).trans_eq (by ring))
