-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_main_public_pathwise_mesh_error_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:12:45.658854+00:00
-- url     : https://prove2.me/submissions/3574322b-9f91-4f94-8fb1-610d09d0c581

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter

theorem solution
    (err ε : ℕ → ℝ) (B : ℝ)
    (hε : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hbound : ∀ k, |err k| ≤ ε k * B) :
    Filter.Tendsto err Filter.atTop (nhds 0) := by
  have hmul : Filter.Tendsto (fun k => ε k * B) Filter.atTop (nhds 0) := by
    simpa using hε.mul_const B
  have habs : Filter.Tendsto (fun k => |err k|) Filter.atTop (nhds 0) :=
    squeeze_zero (fun k => abs_nonneg (err k)) hbound hmul
  exact (tendsto_zero_iff_abs_tendsto_zero err).2 (by
    simpa [Function.comp_def] using habs)
