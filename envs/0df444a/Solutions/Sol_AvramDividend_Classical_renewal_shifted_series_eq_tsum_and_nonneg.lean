-- Prove2me | solution 1 for AvramDividend.Classical.renewal_shifted_series_eq_tsum_and_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T08:18:33.682105+00:00
-- url     : https://prove2.me/submissions/b85cd6d0-512b-48d1-97e7-b2cb5d9ddc90

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order

theorem solution
    (F : ℕ → ℝ) (hF : Summable F) (hF0 : ∀ n : ℕ, 0 ≤ F n) :
    (∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1)) =
      (∑' n : ℕ, F n) ∧
      0 ≤ (∑' n : ℕ, F n) := by
  refine ⟨?_, tsum_nonneg hF0⟩
  set f : ℕ → ℝ := fun n => if n = 0 then (0 : ℝ) else F (n - 1) with hf
  have hs : Summable f := (summable_nat_add_iff 1).mp (by simpa [hf] using hF)
  rw [hs.tsum_eq_zero_add]
  simp [hf]
