-- Prove2me | solution 1 for DeletedPrimes.split_balance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:18:08.718256+00:00
-- url     : https://prove2.me/submissions/4984ce17-f317-4f3a-b326-80d51a243141

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {y α : ℝ} (hy : 0 < y) :
    (y ^ (1 / 2 : ℝ)) ^ α = y ^ (α / 2) ∧ y ^ (1 / 2 : ℝ) * (y ^ (1 / 2 : ℝ)) ^ (α - 1) = y ^ (α / 2) := by
  constructor
  · rw [← Real.rpow_mul hy.le]; ring_nf
  · rw [← Real.rpow_mul hy.le, ← Real.rpow_add hy]; ring_nf
end DeletedPrimes
