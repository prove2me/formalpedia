-- Prove2me | solution 1 for GDPRPrivacy.PriceRise.alpha1_le_alpha2
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-14T13:50:07.195993+00:00
-- url     : https://prove2.me/submissions/b2f29ffa-bfb0-4c2f-b3c8-1866c9473c8c

import Mathlib
import Definitions.Def_GDPRPrivacy_PriceRise_Model
open GDPRPrivacy.PriceRise

theorem solution(x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    alpha1 x ≤ alpha2 x := by
  unfold alpha1 alpha2
  rcases le_total ((1 - 2 * x) / 2) 0 with h | h
  · exact max_le (h.trans (le_max_right _ _)) (le_max_right _ _)
  · have hx : x ≤ 1 / 2 := by linarith
    refine max_le_max ?_ le_rfl
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
