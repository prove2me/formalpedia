-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_ennreal_liminf_scaled_tendsto_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:48:08.012195+00:00
-- url     : https://prove2.me/submissions/9bcee714-baa7-42c2-b3e7-216efc87ba34

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
open scoped ENNReal
noncomputable section

/-- A vanishing source discount leaves the ENNReal Fatou liminf unchanged below. -/
theorem solution
    (u a : ℕ → ℝ≥0∞)
    (ha : Filter.Tendsto a Filter.atTop (nhds (1 : ℝ≥0∞))) :
    Filter.liminf u Filter.atTop ≤
      Filter.liminf (fun n => a n * u n) Filter.atTop := by
  have hmul := ENNReal.le_liminf_mul (u := a) (v := u) (f := atTop)
  change (liminf a atTop) * (liminf u atTop) ≤
    liminf (fun n => a n * u n) atTop at hmul
  simpa only [ha.liminf_eq, one_mul] using hmul
