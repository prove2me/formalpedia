-- Prove2me | solution 1 for BianchiIX.core_small_clock_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:58:57.617966+00:00
-- url     : https://prove2.me/submissions/4b166b77-abc8-4a8e-924c-86249d8c7443

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

private theorem BianchiIX.core_wall_difference_bounds {m u w : ℝ} (hu : 0 ≤ u ∧ u ≤ m)
    (hw : 0 ≤ w ∧ w ≤ m) :
    |u - w| ≤ m ∧ |u - 2 * w| ≤ 2 * m ∧ |3 * w - u| ≤ 3 * m ∧ |2 * u - w| ≤ 2 * m := by
  constructor
  · exact abs_le.mpr ⟨by linarith, by linarith⟩
  constructor
  · exact abs_le.mpr ⟨by linarith, by linarith⟩
  constructor <;> exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem solution {r m u w v : ℝ} (hr : 5 ≤ r)
    (hm : 0 ≤ m ∧ m ≤ 1 / 100) (hu : 0 ≤ u ∧ u ≤ m) (hw : 0 ≤ w ∧ w ≤ m)
    (hv : 0 < v) :
    |2 * (u - w) * (u - 2 * w) / r ^ 3| ≤ m / r ^ 2 ∧
    |-2 * (u - w) / r ^ 2| ≤ 2 * m / r ^ 2 ∧
    |2 * (u - w) / (v * r ^ 2)| ≤ 2 * m / (v * r ^ 2) := by
  have hr0 : 0 < r := by linarith
  obtain ⟨hδ, h2, _, _⟩ := core_wall_difference_bounds hu hw
  have hnum : 2 * |u - w| * |u - 2 * w| ≤ 4 * m ^ 2 := by
    have H := mul_le_mul hδ h2 (abs_nonneg _) hm.1
    nlinarith
  have hfactor : 4 * m / r ≤ 1 := (div_le_one hr0).mpr (by linarith [hm.2])
  constructor
  · calc
      |2 * (u - w) * (u - 2 * w) / r ^ 3| = 2 * |u - w| * |u - 2 * w| / r ^ 3 := by
        simp [abs_mul, abs_div, abs_pow, abs_of_pos hr0]
      _ ≤ 4 * m ^ 2 / r ^ 3 := div_le_div_of_nonneg_right hnum (by positivity)
      _ = (m / r ^ 2) * (4 * m / r) := by ring
      _ ≤ m / r ^ 2 := mul_le_of_le_one_right (div_nonneg hm.1 (sq_nonneg _)) hfactor
  constructor
  · simp only [abs_div, abs_mul, abs_pow, abs_of_pos hr0]
    norm_num
    gcongr
  · rw [abs_div, abs_mul, abs_of_pos (mul_pos hv (sq_pos_of_pos hr0))]
    norm_num
    gcongr
