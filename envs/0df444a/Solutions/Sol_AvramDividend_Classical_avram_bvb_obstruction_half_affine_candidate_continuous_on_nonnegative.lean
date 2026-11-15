-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_half_affine_candidate_continuous_on_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T01:08:11.078203+00:00
-- url     : https://prove2.me/submissions/6f69e3ea-70d4-41be-b9ba-08abc637088b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Real
theorem solution :
    ContinuousOn (fun u : ℝ => if u < 0 then 0 else 1 / 2 + u) (Ici 0) := by
  have hCont : Continuous (fun u : ℝ => (1 / 2 : ℝ) + u) :=
    continuous_const.add continuous_id
  apply hCont.continuousOn.congr
  intro y hy
  have hnot : ¬ y < 0 := not_lt.mpr hy
  simp [hnot]
