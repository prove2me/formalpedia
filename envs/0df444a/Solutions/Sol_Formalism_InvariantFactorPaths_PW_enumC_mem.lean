-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.enumC_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:57.700944+00:00
-- url     : https://prove2.me/submissions/38ab66f4-d6e6-4712-80c5-e2377eacc57d

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_HasLatBasis
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r n : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (Cs : Finset (Fin r)) (a : Fin Cs.card) : enumC Cs a ∈ Cs :=
  Finset.orderEmbOfFin_mem Cs rfl a
end Formalism.InvariantFactorPaths.PW
