-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.mem_perpS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:19:28.380854+00:00
-- url     : https://prove2.me/submissions/dab58743-aaa4-4e4d-b6a9-e1c3ae2572ad

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_OrthogonalIsomorphismHolds

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
variable {p : ℕ} [Fact p.Prime] {σ : Type}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (A : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])) (y : MvPolynomial σ ℚ_[p]) :
    y ∈ perpS A ↔ ∀ x ∈ A, fock p x y = 0 := Iff.rfl
end Formalism.InvariantFactorPaths.PW
