-- Prove2me | solution 1 for DeletedPrimes.count_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:09:34.051144+00:00
-- url     : https://prove2.me/submissions/4f9bc37e-b2e8-4eb4-8584-e1546baf763c

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {x : ℝ} : count ∅ x = ⌊x⌋₊ := by
  classical
  unfold count
  have hall : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊, SFree ∅ n := fun n _ p hp => absurd hp (Set.notMem_empty p)
  rw [Finset.filter_true_of_mem hall]
  simp
end DeletedPrimes
