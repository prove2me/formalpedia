-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.INST.rgl_swp_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:48.127661+00:00
-- url     : https://prove2.me/submissions/c1952f6c-03ba-47d7-b8a4-7eff7294298a

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_GlFirstLineDividedPowers
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_rgl_swp_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.INST
open Formalism.GradedWeylDivisibility Formalism.GM.M Formalism.GM.DimensionMonotonicity Formalism.InvariantFactorPaths.PW
variable (R : Type) [CommRing R] {r n : ℕ}
namespace Formalism.InvariantFactorPaths.INST
theorem _root_.solution {S : Type} [CommRing S] (φ : R →+* S) (f : MvPolynomial (Fin r × Fin n) R) :
    swp S r n (map φ f) = map φ (swp R r n f) := by
  rw [rgl_swp_apply, rgl_swp_apply, map_rename]
end Formalism.InvariantFactorPaths.INST
