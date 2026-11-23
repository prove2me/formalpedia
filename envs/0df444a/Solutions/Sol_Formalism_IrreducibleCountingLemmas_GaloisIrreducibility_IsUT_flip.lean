-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.IsUT.flip
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:03.493251+00:00
-- url     : https://prove2.me/submissions/943e355c-9f32-4221-bd0e-bb0adf8f509b

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Lemmata_TwistedIdempotents_TwistedIdem
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_MemBesselSetZeroIffUpperTriangular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable {K : Type} [Field K] {N : ℕ}
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace IsUT
theorem _root_.solution {A : Matrix (Fin N) (Fin N) K} (h : IsUT A) : IsUT (flipM A) :=
  ⟨fun i => h.1 _, fun i j hij => h.2 _ _ (Fin.rev_lt_rev.mpr hij)⟩
end IsUT
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
