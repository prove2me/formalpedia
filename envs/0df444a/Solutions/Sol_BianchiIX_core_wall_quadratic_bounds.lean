-- Prove2me | solution 1 for BianchiIX.core_wall_quadratic_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:27:19.519072+00:00
-- url     : https://prove2.me/submissions/2435f73b-ab21-4154-9bb3-843ac69d4364

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


/-- Quadratic wall terms retain the strong amplitude and the square of the weak amplitude. -/
theorem solution {m u w : ℝ}
    (hu : 0 ≤ u ∧ u ≤ m) (hw : 0 ≤ w ∧ w ≤ m) :
    |u - w| * |u - 2 * w| ≤ 4 * m * u + 2 * w ^ 2 ∧
    |u - w| * |3 * w - u| ≤ 5 * m * u + 3 * w ^ 2 := by
  have hδ : |u - w| ≤ u + w := by
    simpa only [abs_of_nonneg hu.1, abs_of_nonneg hw.1] using abs_sub u w
  have h2 : |u - 2 * w| ≤ u + 2 * w := by
    calc
      _ ≤ |u| + |2 * w| := abs_sub _ _
      _ = u + 2 * w := by rw [abs_of_nonneg hu.1, abs_of_nonneg (mul_nonneg (by norm_num) hw.1)]
  have h3 : |3 * w - u| ≤ u + 3 * w := by
    calc
      _ ≤ |3 * w| + |u| := abs_sub _ _
      _ = u + 3 * w := by rw [abs_of_nonneg hu.1, abs_of_nonneg (mul_nonneg (by norm_num) hw.1)]; ring
  have hu2 := mul_le_mul_of_nonneg_left hu.2 hu.1
  have huw := mul_le_mul_of_nonneg_left hw.2 hu.1
  constructor
  · have H := mul_le_mul hδ h2 (abs_nonneg _) (add_nonneg hu.1 hw.1)
    nlinarith only [H, hu2, huw]
  · have H := mul_le_mul hδ h3 (abs_nonneg _) (add_nonneg hu.1 hw.1)
    nlinarith only [H, hu2, huw]
