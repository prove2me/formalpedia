-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_strictPastClock_tendsto_left
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:19:06.296405+00:00
-- url     : https://prove2.me/submissions/c9573dd6-eb9d-48bc-9287-bf5a43add2fc

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology
open scoped NNReal

/-- At positive t, the explicit countable pre-t times tend to t
through the strict past; this identifies the left-limit approximants. -/
theorem solution (t : ℝ≥0) (ht : 0 < t) :
    Tendsto (fun n : ℕ => t - t / ((n : ℝ≥0) + 2))
      atTop (𝓝[<] t) := by
  have hdiv : Tendsto
      (fun n : ℕ => t / ((n : ℝ≥0) + 2))
      atTop (𝓝 0) := by
    convert (tendsto_add_atTop_iff_nat 2).2
        (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ≥0) t) using 1
    ext n
    norm_num [Nat.cast_add]
  have hlim : Tendsto
      (fun n : ℕ => t - t / ((n : ℝ≥0) + 2))
      atTop (𝓝 t) := by
    have hc : Tendsto (fun _ : ℕ => t) atTop (𝓝 t) := tendsto_const_nhds
    simpa only [tsub_zero] using hc.sub hdiv
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨hlim, ?_⟩
  exact Filter.Eventually.of_forall fun n => by
    have hp : 0 < t / ((n : ℝ≥0) + 2) := by positivity
    exact tsub_lt_self ht hp
