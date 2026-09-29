-- Prove2me | solution 1 for BookProof.BandEnclosure.nestedBands_le
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T07:37:45.352984+00:00
-- url     : https://prove2.me/submissions/80d859ec-0020-4096-9424-71e0efe1a544

import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.Real.Basic

set_option autoImplicit false

theorem solution {lo hi : ℕ → ℝ}
    (h : ∀ m, Set.Icc (lo (m + 1)) (hi (m + 1)) ⊆ Set.Icc (lo m) (hi m))
    {m n : ℕ} (hmn : m ≤ n) :
    Set.Icc (lo n) (hi n) ⊆ Set.Icc (lo m) (hi m) := by
  induction n, hmn using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ n _ ih => exact Set.Subset.trans (h n) ih

#print axioms solution
