-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.rev_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:51:03.721487+00:00
-- url     : https://prove2.me/submissions/f5ff1c4c-8830-49b9-8bd4-47b03a730159

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRGoodDualStable

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
theorem _root_.solution {h : K[X]} (h0 : h.coeff 0 ≠ 0) : h.reverse.natDegree = h.natDegree := by
  rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr h0), Nat.sub_zero]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
