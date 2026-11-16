-- Prove2me | solution 1 for DiagonalMachine.depth_persists
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:55:34.193832+00:00
-- url     : https://prove2.me/submissions/c206f9fe-06b9-4531-ac18-351e7c1f640d

import Mathlib
open MeasureTheory Set

theorem solution (a : ℕ → ℝ)
    (hstep : ∀ n, a n < 0 → a (n+1) ≤ a n)
    (k : ℕ) (hk : a k < 0) : ∀ j, a (k+j) ≤ a k := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have hneg : a (k+j) < 0 := lt_of_le_of_lt ih hk
    simpa [Nat.add_assoc] using le_trans (hstep (k+j) hneg) ih
