-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.span_isomorphism_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:34:04.39182+00:00
-- url     : https://prove2.me/submissions/4b52fed6-eb19-47f1-b431-73748cf8c63f

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_OrthogonalIsomorphismHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_pol_le_iSup
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_monomial_mem_pol


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
theorem _root_.solution : SpanIso := by
  intro p _ N r LL j Cs
  rw [eq_top_iff]
  intro x _
  rw [x.as_sum]
  refine Submodule.sum_mem _ fun m _ => ?_
  exact pol_le_iSup LL _ j Cs (monomial_mem_pol LL m _)
end Formalism.InvariantFactorPaths.PW
