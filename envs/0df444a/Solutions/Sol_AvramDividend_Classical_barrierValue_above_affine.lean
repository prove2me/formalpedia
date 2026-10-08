-- Prove2me | solution 1 for AvramDividend.Classical.barrierValue_above_affine
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:38:10.042662+00:00
-- url     : https://prove2.me/submissions/adbe689c-940b-4749-8fa3-6e7d06126246

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

theorem solution (W : ℝ → ℝ) (a x : ℝ)
    (ha : 0 ≤ a) (hax : a < x) :
    barrierValue W a x = (x - a) + barrierValue W a a := by
  have hx : 0 ≤ x := le_trans ha (le_of_lt hax)
  have hxnotneg : ¬ x < 0 := not_lt.mpr hx
  have hanotneg : ¬ a < 0 := not_lt.mpr ha
  have hxnotle : ¬ x ≤ a := not_le.mpr hax
  simp [barrierValue, hxnotneg, hanotneg, hxnotle]
