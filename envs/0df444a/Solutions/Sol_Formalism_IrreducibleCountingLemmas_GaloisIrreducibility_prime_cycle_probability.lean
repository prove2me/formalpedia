-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.prime_cycle_probability
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:59:38.061478+00:00
-- url     : https://prove2.me/submissions/1de85443-8511-47cf-af82-e9d7ce27cd39

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleProbPrime
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_prime_cycle_perm_count

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Equiv Equiv.Perm Finset
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : CycleProbPrime := by
  intro N p hp hpN hN2
  exact prime_cycle_perm_count N p hp hpN hN2 _ (fun σ => by simp)
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
