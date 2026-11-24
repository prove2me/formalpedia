-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.TW.Idx.ord_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:52:07.547873+00:00
-- url     : https://prove2.me/submissions/2ebfc851-b9a4-49db-acaa-3cde788fd58a

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWIndexAdditive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.TW
open Formalism.IrreducibleCountingLemmas.TW.Idx
variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
namespace Formalism.IrreducibleCountingLemmas.TW.Idx
theorem _root_.solution {ι : Type} (s : Finset ι) (a : ι → O) (ha : ∀ i, a i ≠ 0) :
    Ring.ord O (∏ i ∈ s, a i) = ∑ i ∈ s, Ring.ord O (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      Ring.ord_mul' O (mem_nonZeroDivisors_of_ne_zero (ha i)), ih]
end Formalism.IrreducibleCountingLemmas.TW.Idx
