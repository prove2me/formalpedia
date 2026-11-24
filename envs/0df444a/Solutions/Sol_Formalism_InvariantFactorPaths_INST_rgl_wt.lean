-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.INST.rgl_wt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:48.111879+00:00
-- url     : https://prove2.me/submissions/fba5270b-0995-43b3-976e-33feb6d7fc85

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_GlFirstLineDividedPowers
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_rgl_mapDomain_apply

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
variable {p : ℕ} [Fact p.Prime] {r n : ℕ}
namespace Formalism.InvariantFactorPaths.INST
theorem _root_.solution (ν : Fin n → ℕ) (a : Fin r) (m : Fin r × Fin n →₀ ℕ) :
    wt (vecL ν) n a (Finsupp.mapDomain (Equiv.prodComm (Fin r) (Fin n)) m) = (rowDeg m a : ℤ) := by
  unfold wt rowDeg
  push_cast
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [if_pos s.isLt, rgl_mapDomain_apply]
  rfl
end Formalism.InvariantFactorPaths.INST
