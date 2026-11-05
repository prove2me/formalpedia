-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_main_original_two_stage_mesh_error_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:32:33.791038+00:00
-- url     : https://prove2.me/submissions/03b10bdf-874c-4f58-83de-ce31422b52a8

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter

/-- The original weighted C1 error and marked-jump translation tails vanish
together under the finite BV variation envelope and summable jump tail. -/
theorem solution
    (err ε tail : ℕ → ℝ) (B K : ℝ)
    (hε : Filter.Tendsto ε Filter.atTop (nhds 0))
    (htail : Filter.Tendsto tail Filter.atTop (nhds 0))
    (hbound : ∀ k, |err k| ≤ ε k * B + 2 * K * tail k) :
    Filter.Tendsto err Filter.atTop (nhds 0) := by
  have hA : Filter.Tendsto (fun k => ε k * B) Filter.atTop (nhds 0) := by
    simpa using hε.mul_const B
  have hB : Filter.Tendsto (fun k => 2 * K * tail k)
      Filter.atTop (nhds 0) := by
    simpa [mul_assoc] using htail.const_mul (2 * K)
  have hAB : Filter.Tendsto (fun k => ε k * B + 2 * K * tail k)
      Filter.atTop (nhds 0) := by simpa using hA.add hB
  have hAbs : Filter.Tendsto (fun k => |err k|)
      Filter.atTop (nhds 0) :=
    squeeze_zero (fun k => abs_nonneg (err k)) hbound hAB
  exact (tendsto_zero_iff_abs_tendsto_zero err).2 (by
    simpa [Function.comp_def] using hAbs)
