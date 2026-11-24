-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.enumC_surj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:57.850686+00:00
-- url     : https://prove2.me/submissions/dd4edca8-ea1b-4b4c-bae8-9e904b1c916f

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
theorem _root_.solution (Cs : Finset (Fin r)) {c : Fin r} (hc : c ∈ Cs) : ∃ a, enumC Cs a = c := by
  have h : c ∈ Set.range (Cs.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]; exact hc
  exact h
end Formalism.InvariantFactorPaths.PW
