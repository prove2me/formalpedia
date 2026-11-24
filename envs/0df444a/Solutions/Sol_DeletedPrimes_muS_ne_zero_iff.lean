-- Prove2me | solution 1 for DeletedPrimes.muS_ne_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:50:30.201138+00:00
-- url     : https://prove2.me/submissions/18677b30-1581-48a2-b2e8-57a7af555a94

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}
namespace DeletedPrimes
theorem _root_.solution {d : ℕ} :
    muS S d ≠ 0 ↔ Squarefree d ∧ ∀ p ∈ d.primeFactors, p ∈ S := by
  unfold muS
  split_ifs with h
  · rw [ArithmeticFunction.moebius_ne_zero_iff_squarefree]; tauto
  · simp only [ne_eq, not_true_eq_false, false_iff]; tauto
end DeletedPrimes
