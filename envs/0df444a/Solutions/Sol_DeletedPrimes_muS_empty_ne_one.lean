-- Prove2me | solution 1 for DeletedPrimes.muS_empty_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:09:35.278887+00:00
-- url     : https://prove2.me/submissions/2afc26f5-dc33-4760-8de3-05d421e376a5

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {d : ℕ} (hd : d ≠ 1) : muS ∅ d = 0 := by
  unfold muS
  rcases Nat.lt_or_ge d 2 with h | h
  · interval_cases d
    · simp
    · exact absurd rfl hd
  · obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr (by omega : 1 < d)
    split_ifs with hall
    · exact absurd (hall p hp) (Set.notMem_empty p)
    · rfl
end DeletedPrimes
