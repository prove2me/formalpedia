-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_negative_test_weighted_log_vanishes_near_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:47:04.689386+00:00
-- url     : https://prove2.me/submissions/a81df41b-0b03-41b3-82b6-3380fc3e5952

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology

theorem solution
    (f : ℝ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hfsupp : ∀ y : ℝ, -ε < y → f y = 0) :
    (fun z : ℝ => f (Real.log z) / (z - 1) ^ 4) =ᶠ[nhds (1 : ℝ)]
      (fun _ : ℝ => 0) := by
  have hlt : -ε < Real.log (1 : ℝ) := by
    simpa using (neg_lt_zero.mpr hε)
  have hopen : Ioi (-ε) ∈ nhds (Real.log (1 : ℝ)) :=
    isOpen_Ioi.mem_nhds hlt
  have hlog : ContinuousAt Real.log (1 : ℝ) :=
    Real.continuousAt_log (by norm_num)
  have hev : ∀ᶠ z in nhds (1 : ℝ), Real.log z ∈ Ioi (-ε) :=
    hlog.tendsto.eventually hopen
  filter_upwards [hev] with z hz
  have hy : -ε < Real.log z := hz
  simp [hfsupp (Real.log z) hy]
