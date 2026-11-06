-- Prove2me | solution 1 for BianchiIX.core_small_radius_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:04:09.771904+00:00
-- url     : https://prove2.me/submissions/1315d9db-de3c-49b2-a734-d68ea8d1431b

import Theorems.Thm_BianchiIX_core_small_coupling_derivatives
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

theorem solution {r m u v w s c : ℝ} (hr : 5 ≤ r)
    (hm : 0 ≤ m ∧ m ≤ 1 / 100) (hu : 0 ≤ u ∧ u ≤ m) (hw : 0 ≤ w ∧ w ≤ m)
    (hv : 1 ≤ v ∧ v ≤ r) (hs : 0 ≤ s ∧ s ≤ 1) (hc : |c| ≤ 1) :
    |-u * (s - w / r) + c * (u - w) * (3 * w - u) / r ^ 2| ≤ 2 * m ∧
    |(-(v - 2 * u + w) + 2 * c * (u - w) / r) + v| ≤ 3 * m ∧
    |-u / v - 2 * c * (u - w) / (r * v)| ≤ 2 * m / v := by
  have hr0 : 0 < r := by linarith
  have hv0 : 0 < v := by linarith [hv.1]
  obtain ⟨hδ, _, h3, h2⟩ := core_wall_difference_bounds hu hw
  have hcd : |c| * |u - w| ≤ m := (mul_le_of_le_one_left (abs_nonneg _) hc).trans hδ
  have hnum : |c| * |u - w| * |3 * w - u| ≤ 3 * m ^ 2 := by
    have H := mul_le_mul hcd h3 (abs_nonneg _) hm.1
    nlinarith
  have hCR := (core_small_coupling_derivatives hr hm hu hw hv hs).1
  have he : |c * (u - w) * (3 * w - u) / r ^ 2| ≤ m := by
    rw [abs_div, abs_mul, abs_mul, abs_pow, abs_of_pos hr0]
    apply (div_le_iff₀ (sq_pos_of_pos hr0)).mpr
    have H : 3 * m ^ 2 ≤ m * r ^ 2 := by
      have H' : 3 * m ≤ r ^ 2 := by nlinarith [sq_nonneg (r - 5), hm.2]
      nlinarith [mul_nonneg hm.1 (sub_nonneg.mpr H')]
    exact hnum.trans H
  have he' : |2 * c * (u - w) / r| ≤ m := by
    simp only [abs_div, abs_mul, abs_of_pos hr0]
    norm_num
    apply (div_le_iff₀ hr0).mpr
    nlinarith [mul_nonneg hm.1 (show 0 ≤ r - 2 by linarith)]
  have he'' : |2 * c * (u - w) / (r * v)| ≤ m / v := by
    rw [← div_div, abs_div, abs_of_pos hv0]
    exact div_le_div_of_nonneg_right he' hv0.le
  constructor
  · have H := abs_add_le (-u * (s - w / r)) (c * (u - w) * (3 * w - u) / r ^ 2)
    have H' : |-u * (s - w / r)| ≤ u := by simpa only [neg_mul, abs_neg] using hCR
    linarith [hu.2]
  constructor
  · rw [show -(v - 2 * u + w) + 2 * c * (u - w) / r + v =
      (2 * u - w) + 2 * c * (u - w) / r by ring]
    have H := abs_add_le (2 * u - w) (2 * c * (u - w) / r)
    linarith
  · have H := abs_sub (-u / v) (2 * c * (u - w) / (r * v))
    have H' : |(-u / v)| ≤ m / v := by
      rw [abs_div, abs_neg, abs_of_nonneg hu.1, abs_of_pos hv0]
      exact div_le_div_of_nonneg_right hu.2 hv0.le
    calc
      _ ≤ m / v + m / v := H.trans (add_le_add H' he'')
      _ = 2 * m / v := by ring
