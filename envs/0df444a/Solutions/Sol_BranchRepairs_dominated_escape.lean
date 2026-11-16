-- Prove2me | solution 1 for BranchRepairs.dominated_escape
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T03:29:28.345584+00:00
-- url     : https://prove2.me/submissions/9d6738b6-bcd4-409d-986f-bd6d65f6d3a2

import Mathlib
open Filter Topology

theorem solution (f : ℕ → ℕ → ℝ) (bound : ℕ → ℝ)
    (hs : Summable bound)
    (hpoint : ∀ j, Tendsto (fun m => f m j) atTop (𝓝 0))
    (hbound : ∀ᶠ m in atTop, ∀ j, ‖f m j‖ ≤ bound j) :
    Tendsto (fun m => ∑' j, f m j) atTop (𝓝 0) := by
  simpa using tendsto_tsum_of_dominated_convergence hs hpoint hbound

-- Exact rational margins used in the two heat-kernel ranges.
