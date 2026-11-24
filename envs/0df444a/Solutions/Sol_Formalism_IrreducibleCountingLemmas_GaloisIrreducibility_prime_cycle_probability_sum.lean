-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.prime_cycle_probability_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:11:52.502401+00:00
-- url     : https://prove2.me/submissions/99406f81-7fe8-4701-9151-7f8f90b52e32

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRJoints
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleProbPrime
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleProbSum
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_cycleProbSum_of_cycleProbPrime
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_prime_cycle_probability


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : CycleProbSum := cycleProbSum_of_cycleProbPrime prime_cycle_probability
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
