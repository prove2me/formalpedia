-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.prime_reciprocal_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:16:08.697126+00:00
-- url     : https://prove2.me/submissions/f3055449-d2bf-4b3b-a57e-2b3496b1bf30

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeRecipSum
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_PrimeCountingLemmas_S_small
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_PrimeCountingLemmas_S_large
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_PrimeCountingLemmas_four_le_log

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
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : PrimeRecipSum := by
  intro N hN
  change 1 / (5 * Real.log N) ≤ PrimeCountingLemmas.S N
  by_cases h : N < 20000
  · have h4 := PrimeCountingLemmas.four_le_log N hN
    exact (one_div_le_one_div_of_le (by norm_num) (by linarith)).trans (PrimeCountingLemmas.S_small N hN h)
  · exact PrimeCountingLemmas.S_large N (by omega)
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
