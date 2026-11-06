-- Prove2me | solution 1 for BianchiIX.core_clock_quotient_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:00:02.092582+00:00
-- url     : https://prove2.me/submissions/112bc82f-73ed-4cd2-bc8a-be821c28efb1

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
    (hx : |x| ≤ A) (hy : |y| ≤ B) : |x / d - y / d ^ 2| ≤ 3 / 2 * A + 2 * B := by
  have hd0 : 0 < d := by linarith
  have hA : 0 ≤ A := (abs_nonneg _).trans hx
  have hB : 0 ≤ B := (abs_nonneg _).trans hy
  have hdx : |x / d| ≤ 3 / 2 * A := by
    rw [abs_div, abs_of_pos hd0, div_le_iff₀ hd0]
    nlinarith [mul_nonneg hA (show 0 ≤ d - 2 / 3 by linarith)]
  have hdy : |y / d ^ 2| ≤ 2 * B := by
    rw [abs_div, abs_pow, abs_of_pos hd0, div_le_iff₀ (sq_pos_of_pos hd0)]
    have hsq : 1 / 2 ≤ d ^ 2 := by nlinarith
    nlinarith [mul_nonneg hB (sub_nonneg.mpr hsq)]
  exact (abs_sub _ _).trans (add_le_add hdx hdy)
