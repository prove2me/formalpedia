-- Prove2me | solution 1 for BianchiIX.core_amplitude_radius_numerators
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:29:31.985017+00:00
-- url     : https://prove2.me/submissions/c6480d53-5872-460f-a90a-226360885722

import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Theorems.Thm_BianchiIX_core_small_coupling_derivatives
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

noncomputable section
open BianchiIX

section
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

end
end

/-- Radius-row numerators with the weak wall kept at its correct power and scale. -/
theorem solution {r m u v w s c : ℝ} (hr : 5 ≤ r)
    (hm : 0 ≤ m ∧ m ≤ 1 / 100) (hu : 0 ≤ u ∧ u ≤ m) (hw : 0 ≤ w ∧ w ≤ m)
    (hv : 1 ≤ v ∧ v ≤ r) (hs : 0 ≤ s ∧ s ≤ 1) (hc : |c| ≤ 1) :
    |-u * (s - w / r) + c * (u - w) * (3 * w - u) / r ^ 2| ≤ 2 * u + 3 * w ^ 2 / r ^ 2 ∧
    |(-(v - 2 * u + w) + 2 * c * (u - w) / r) + v - v * (1 - coreClockFactor r u w)| ≤
      4 * (u + w) ∧
    |v * (-u / v - 2 * c * (u - w) / (r * v))| ≤ 2 * (u + w / r) := by
  have hr0 : 0 < r := by linarith only [hr]
  have hv0 : 0 < v := by linarith only [hv.1]
  have hδ : |u - w| ≤ u + w := by
    calc
      _ ≤ |u| + |w| := abs_sub _ _
      _ = u + w := by rw [abs_of_nonneg hu.1, abs_of_nonneg hw.1]
  have hδm := (core_wall_difference_bounds hu hw).1
  have hδ2 : (u - w) ^ 2 ≤ m * (u + w) := by
    have H := mul_le_mul hδm hδ (abs_nonneg _) hm.1
    simpa only [← sq, sq_abs] using H
  have hcd : |c| * |u - w| ≤ u + w := (mul_le_of_le_one_left (abs_nonneg _) hc).trans hδ
  have hterm : |2 * c * (u - w) / r| ≤ 2 * (u + w) / r := by
    simp only [abs_div, abs_mul, abs_of_pos hr0]
    norm_num
    exact div_le_div_of_nonneg_right (by linarith only [hcd]) hr0.le
  have hterm' : |2 * c * (u - w) / r| ≤ u + w := by
    apply hterm.trans
    apply (div_le_iff₀ hr0).mpr
    nlinarith only [mul_nonneg (add_nonneg hu.1 hw.1) (show 0 ≤ r - 2 by linarith only [hr])]
  have hclock : |v * (1 - coreClockFactor r u w)| ≤ u + w := by
    have hid : 1 - coreClockFactor r u w = (u - w) ^ 2 / r ^ 2 := by unfold coreClockFactor; ring
    rw [hid, abs_of_nonneg (by positivity)]
    calc
      _ ≤ r * (m * (u + w) / r ^ 2) := mul_le_mul hv.2
        (div_le_div_of_nonneg_right hδ2 (sq_nonneg _)) (by positivity) hr0.le
      _ = (m / r) * (u + w) := by field_simp
      _ ≤ u + w := mul_le_of_le_one_left (add_nonneg hu.1 hw.1)
        ((div_le_one hr0).mpr (by linarith only [hm.2, hr]))
  constructor
  · have hcoupling := (core_small_coupling_derivatives hr hm hu hw hv hs).1
    have hsecond : |c * (u - w) * (3 * w - u) / r ^ 2| ≤
        u + 3 * w ^ 2 / r ^ 2 := by
      calc
        _ = |c| * (|u - w| * |3 * w - u|) / r ^ 2 := by
          simp [abs_mul, abs_div, abs_pow, abs_of_pos hr0]
          ring
        _ ≤ (5 * m * u + 3 * w ^ 2) / r ^ 2 := div_le_div_of_nonneg_right
          ((mul_le_of_le_one_left (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hc).trans
            (core_wall_quadratic_bounds hu hw).2) (sq_nonneg _)
        _ ≤ u + 3 * w ^ 2 / r ^ 2 := by
          have hcoeff : 5 * m / r ^ 2 ≤ 1 := by
            apply (div_le_one (sq_pos_of_pos hr0)).mpr
            nlinarith only [hr, hm.2, sq_nonneg (r - 5)]
          calc
            _ = (5 * m / r ^ 2) * u + 3 * w ^ 2 / r ^ 2 := by ring
            _ ≤ u + 3 * w ^ 2 / r ^ 2 := add_le_add (mul_le_of_le_one_left hu.1 hcoeff) (le_refl _)
    have H := abs_add_le (-u * (s - w / r)) (c * (u - w) * (3 * w - u) / r ^ 2)
    have hfirst : |-u * (s - w / r)| ≤ u := by simpa only [neg_mul, abs_neg] using hcoupling
    linarith only [H, hfirst, hsecond]
  constructor
  · rw [show -(v - 2 * u + w) + 2 * c * (u - w) / r + v =
      (2 * u - w) + 2 * c * (u - w) / r by ring]
    have hfirst : |2 * u - w| ≤ 2 * (u + w) := by
      apply abs_le.mpr
      constructor <;> linarith only [hu.1, hw.1]
    have H := abs_sub ((2 * u - w) + 2 * c * (u - w) / r) (v * (1 - coreClockFactor r u w))
    have H' := abs_add_le (2 * u - w) (2 * c * (u - w) / r)
    linarith only [H, H', hfirst, hterm', hclock]
  · rw [show v * (-u / v - 2 * c * (u - w) / (r * v)) = -u - 2 * c * (u - w) / r by field_simp]
    have H := abs_sub (-u) (2 * c * (u - w) / r)
    rw [abs_neg, abs_of_nonneg hu.1] at H
    have hU : 2 * u / r ≤ u := by
      apply (div_le_iff₀ hr0).mpr
      nlinarith only [mul_nonneg hu.1 (show 0 ≤ r - 2 by linarith only [hr])]
    rw [mul_add, add_div] at hterm
    rw [show 2 * w / r = 2 * (w / r) by ring] at hterm
    linarith only [H, hterm, hU]
