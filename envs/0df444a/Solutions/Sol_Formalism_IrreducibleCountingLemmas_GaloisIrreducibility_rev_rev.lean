-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.rev_rev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:06:09.329095+00:00
-- url     : https://prove2.me/submissions/c0c114f6-6c18-482f-b211-a41659dfc6ee

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRGoodDualStable
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_rev_natDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable {K : Type} [Field K]
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution {h : K[X]} (h0 : h.coeff 0 ≠ 0) : h.reverse.reverse = h := by
  ext n
  rw [coeff_reverse, coeff_reverse, rev_natDegree h0, revAt_invol]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
