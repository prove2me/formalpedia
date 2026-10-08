-- Prove2me | solution 1 for AvramDividend.Classical.barrierValue_zero_affine_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:34:17.050985+00:00
-- url     : https://prove2.me/submissions/cf010195-8533-4b06-8973-3407d4bf6660

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

theorem solution (W : ℝ → ℝ) (x : ℝ) (hx : 0 ≤ x) :
    barrierValue W 0 x = x + barrierValue W 0 0 := by
  by_cases hxzero : x = 0
  · subst x
    simp
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
    have hxnotneg : ¬ x < 0 := not_lt.mpr (le_of_lt hxpos)
    have hxnotle : ¬ x ≤ 0 := not_le.mpr hxpos
    simp [barrierValue, hxnotneg, hxnotle]
