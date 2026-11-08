-- Prove2me | solution 1 for AvramDividend.Classical.avram_gen10_affine_payoff_payout_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T11:10:53.497516+00:00
-- url     : https://prove2.me/submissions/017199e1-b286-4127-825a-efc331df4ac3

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical
noncomputable section

theorem solution
    (r a : ℝ) (hr : 0 ≤ r) (ha : 0 ≤ a)
    (hpost : 0 ≤ r - a) :
    a ≤
      (if r < 0 then (0 : ℝ) else 1 + r) -
      (if r - a < 0 then (0 : ℝ) else 1 + (r - a)) := by
  have hn : ¬ r < 0 := not_lt.mpr hr
  have hn' : ¬ r - a < 0 := not_lt.mpr hpost
  simp only [if_neg hn, if_neg hn']
  linarith
