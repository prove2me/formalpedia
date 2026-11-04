-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_negative_test_weighted_log_vanishes_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:52:47.780801+00:00
-- url     : https://prove2.me/submissions/bc256621-682f-455e-8773-d8558263d408

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology

theorem solution
    (f : ℝ → ℝ) (a : ℝ)
    (hflower : ∀ y : ℝ, y < a → f y = 0)
    (hfzero : f 0 = 0) :
    (fun z : ℝ => f (Real.log z) / (z - 1) ^ 4) =ᶠ[
      nhdsWithin (0 : ℝ) (Ici 0)] (fun _ : ℝ => 0) := by
  have he : (0 : ℝ) < Real.exp a := Real.exp_pos a
  have hevent : ∀ᶠ z in nhds (0 : ℝ), z < Real.exp a :=
    eventually_lt_nhds he
  filter_upwards [hevent.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz hz0
  have hnonneg : 0 ≤ z := hz0
  rcases lt_or_eq_of_le hnonneg with hpos | heq
  · have hlog : Real.log z < a :=
      (Real.log_lt_iff_lt_exp hpos).mpr hz
    simp [hflower (Real.log z) hlog]
  · subst z
    simp [hfzero]
