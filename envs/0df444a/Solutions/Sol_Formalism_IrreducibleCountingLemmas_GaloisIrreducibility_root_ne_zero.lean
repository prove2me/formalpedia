-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.root_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:58:47.493522+00:00
-- url     : https://prove2.me/submissions/10a0a583-282b-4fe0-9bd0-f489320eb4c4

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRFrobOrbitIrred
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRSamePartCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CoeffZeroNeZeroOfIrreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L]
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution {f : K[X]} (h0 : f.coeff 0 ≠ 0) {x : L} (hx : aeval x f = 0) : x ≠ 0 := by
  intro h
  rw [h, ← Polynomial.coeff_zero_eq_aeval_zero'] at hx
  exact h0 ((map_eq_zero_iff _ (algebraMap K L).injective).1 hx)
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
