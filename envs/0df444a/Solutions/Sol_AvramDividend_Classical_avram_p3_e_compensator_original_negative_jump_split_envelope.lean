-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_e_compensator_original_negative_jump_split_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:06:47.849317+00:00
-- url     : https://prove2.me/submissions/0c8064f2-de91-430c-ad17-cd96b3791dd8

import Mathlib
open Set
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
(w : ℝ → ℝ) (a b L R : ℝ)
(ha : 0 < a) (hab : a ≤ b) (hL : 0 ≤ L) (hR : 0 ≤ R)
(hLip : ∀ u ∈ Set.Icc (a / 2) b, ∀ v ∈ Set.Icc (a / 2) b,
    |w u - w v| ≤ L * |u - v|)
(hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
(y z : ℝ) (hy : y ∈ Set.Icc a b) (hz : z < 0) :
|w (y + z) - w y| ≤ if -(a / 2) ≤ z then L * |z| else 2 * R := by
  by_cases hsmall : -(a / 2) ≤ z
  · have hySmall : y ∈ Icc (a / 2) b := by
      constructor
      · linarith [hy.1, ha]
      · exact hy.2
    have hyz : y + z ∈ Icc (a / 2) b := by
      constructor
      · linarith [hy.1, hsmall]
      · linarith [hy.2, hz]
    have h := hLip (y + z) hyz y hySmall
    simpa [hsmall, add_sub_cancel_left] using h
  · have hyzLe : y + z ≤ b := by
      linarith [hy.2, hz]
    have hyBound := hWbound y hy.2
    have hyzBound := hWbound (y + z) hyzLe
    have htri : |w (y + z) - w y| ≤ |w (y + z)| + |w y| := by
      simpa [sub_zero, zero_sub, abs_neg] using
        (abs_sub_le (w (y + z)) 0 (w y))
    have hlarge : |w (y + z) - w y| ≤ 2 * R := by
      calc
        |w (y + z) - w y| ≤ |w (y + z)| + |w y| := htri
        _ ≤ R + R := add_le_add hyzBound hyBound
        _ = 2 * R := by ring
    simpa [hsmall] using hlarge
