-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.weylLat_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:50:21.444965+00:00
-- url     : https://prove2.me/submissions/d7768071-75b6-4cf4-a15b-3089015b565e

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_LatData
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CommProjectionHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_ZpClosedToAddSubgroup

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
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (LL : Letters N) (j : ℕ) (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) (c d : Fin r) (hcd : c ≠ d)
    (k : ℕ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hx : x ∈ WeylLat p LL j h) :
    (((k.factorial : ℚ_[p]))⁻¹) • ((glAct p LL j c d) ^ k) x ∈ WeylLat p LL j h := by
  rw [WeylLat, Submodule.mem_sInf] at hx ⊢
  exact fun L hL => hL.2 c d hcd k x (hx L hL)
end Formalism.InvariantFactorPaths.PW
