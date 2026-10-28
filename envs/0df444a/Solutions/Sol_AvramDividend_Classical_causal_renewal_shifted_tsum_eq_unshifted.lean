-- Prove2me | solution 1 for AvramDividend.Classical.causal_renewal_shifted_tsum_eq_unshifted
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:58:06.312189+00:00
-- url     : https://prove2.me/submissions/bbed0c1f-b7d4-4679-8d02-cd1ecfa81743

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
set_option maxHeartbeats 1000000

theorem solution
    (F : ℕ → ℝ) (hF : Summable F) :
    (∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1)) =
      ∑' n : ℕ, F n := by
  set f : ℕ → ℝ := fun n => if n = 0 then (0 : ℝ) else F (n - 1) with hf
  have hs : Summable f := (summable_nat_add_iff 1).mp (by simpa [hf] using hF)
  rw [hs.tsum_eq_zero_add]
  simp [hf]
