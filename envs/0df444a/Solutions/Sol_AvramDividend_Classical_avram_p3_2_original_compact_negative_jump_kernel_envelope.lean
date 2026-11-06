-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_compact_negative_jump_kernel_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T08:51:38.794957+00:00
-- url     : https://prove2.me/submissions/8752c9ca-2684-41a4-a802-5c1d79522ed9

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- Source-exact compact BV nonlinear negative-mark kernel envelope:
small marks are first-order Lipschitz, large marks uniformly bounded. -/
theorem solution
    (w : ℝ → ℝ) (a b L R : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hLip : ∀ u ∈ Set.Icc (a / 2) b, ∀ v ∈ Set.Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
    (y z : ℝ) (hy : y ∈ Set.Icc a b) (hz : z < 0) :
    |w (y + z) - w y| ≤
      if -(a / 2) ≤ z then L * |z| else 2 * R := by
  by_cases hzSmall : -(a / 2) ≤ z
  · have hyLeft : y ∈ Set.Icc (a / 2) b := by
      constructor
      · linarith only [ha, hy.1]
      · exact hy.2
    have hyShift : y + z ∈ Set.Icc (a / 2) b := by
      constructor
      · linarith only [hy.1, hzSmall]
      · linarith only [hy.2, hz]
    have h := hLip (y + z) hyShift y hyLeft
    have hid : y + z - y = z := by ring
    rw [hid] at h
    simpa [hzSmall] using h
  · have hW1 := hWbound (y + z) (by linarith only [hy.2, hz])
    have hW2 := hWbound y hy.2
    have hTriangle : |w (y + z) - w y| ≤
        |w (y + z)| + |w y| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        (abs_add_le (w (y + z)) (-w y))
    have hBound : |w (y + z) - w y| ≤ 2 * R := by
      calc
        _ ≤ |w (y + z)| + |w y| := hTriangle
        _ ≤ R + R := add_le_add hW1 hW2
        _ = 2 * R := by ring
    simpa [hzSmall] using hBound
