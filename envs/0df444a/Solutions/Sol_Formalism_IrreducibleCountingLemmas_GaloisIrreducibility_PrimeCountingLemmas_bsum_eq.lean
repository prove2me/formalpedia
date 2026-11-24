-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas.bsum_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:05:58.296213+00:00
-- url     : https://prove2.me/submissions/80f57cd8-7705-4edd-aeb7-2f7c03d5019a

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeRecipSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Nat
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas
theorem _root_.solution (t : ℕ → ℕ) : ∀ k lo, bsum t k lo = ∑ p ∈ Finset.Ico lo (lo + 2 ^ k), t p := by
  intro k
  induction k with
  | zero =>
    intro lo
    simp [bsum]
  | succ k ih =>
    intro lo
    rw [bsum, ih, ih, Finset.sum_Ico_consecutive _ (Nat.le_add_right _ _) (Nat.le_add_right _ _), pow_succ,
      show lo + 2 ^ k + 2 ^ k = lo + 2 ^ k * 2 by ring]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas
