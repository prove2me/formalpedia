-- Prove2me | solution 1 for BianchiIX.core_amplitude_clock_products
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:29:15.753179+00:00
-- url     : https://prove2.me/submissions/584bb517-1286-401d-b86b-bf49d2a24914

import Theorems.Thm_BianchiIX_core_wall_quadratic_bounds
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


theorem solution {r m u w g : ℝ} (hr : 5 ≤ r)
    (hm : 0 ≤ m ∧ m ≤ 1 / 100) (hu : 0 ≤ u ∧ u ≤ m) (hw : 0 ≤ w ∧ w ≤ m)
    (hg : |g| ≤ 2 * r * m) :
    |g * (2 * (u - w) * (u - 2 * w) / r ^ 3)| ≤ (u + w ^ 2 / r ^ 2) / 10 ∧
    |g * (-2 * (u - w) / r ^ 2)| ≤ (u + w / r) / 10 := by
  have hr0 : 0 < r := by linarith only [hr]
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr0
  have hm0 := hm.1
  have hu0 := hu.1
  have hw0 := hw.1
  have hm2 : m ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := (sq_le_sq₀ hm.1 (by norm_num)).mpr hm.2
  have hδ : |u - w| ≤ u + w := by
    calc
      _ ≤ |u| + |w| := abs_sub _ _
      _ = u + w := by rw [abs_of_nonneg hu.1, abs_of_nonneg hw.1]
  have hucoef : 16 * m ^ 2 / r ^ 2 ≤ 1 / 10 := by
    apply (div_le_iff₀ hr2).mpr
    nlinarith only [hm2, hr, sq_nonneg (r - 5)]
  have hwcoef : 8 * m ≤ 1 / 10 := by linarith only [hm.2]
  have h4m : 4 * m ≤ 1 / 10 := by linarith only [hm.2]
  have h4mr : 4 * m / r ≤ 1 / 10 := by
    apply (div_le_iff₀ hr0).mpr
    linarith only [hr, hm.2]
  constructor
  · calc
      _ = |g| * (2 * (|u - w| * |u - 2 * w|) / r ^ 3) := by
        simp only [abs_mul, abs_div, abs_pow, abs_of_pos hr0, show |(2 : ℝ)| = 2 by norm_num]
        ring
      _ ≤ (2 * r * m) * (2 * (4 * m * u + 2 * w ^ 2) / r ^ 3) := by
        apply mul_le_mul hg ?_ (by positivity) (by positivity)
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (core_wall_quadratic_bounds hu hw).1 (by norm_num)) (by positivity)
      _ = (16 * m ^ 2 / r ^ 2) * u + (8 * m) * (w ^ 2 / r ^ 2) := by field_simp; ring
      _ ≤ (1 / 10) * u + (1 / 10) * (w ^ 2 / r ^ 2) := by gcongr
      _ = (u + w ^ 2 / r ^ 2) / 10 := by ring
  · calc
      _ = |g| * (2 * |u - w| / r ^ 2) := by
        simp [abs_mul, abs_div, abs_pow, abs_of_pos hr0]
      _ ≤ (2 * r * m) * (2 * (u + w) / r ^ 2) := by
        apply mul_le_mul hg ?_ (by positivity) (by positivity)
        gcongr
      _ = (4 * m / r) * u + (4 * m) * (w / r) := by field_simp; ring
      _ ≤ (1 / 10) * u + (1 / 10) * (w / r) := by gcongr
      _ = (u + w / r) / 10 := by ring
