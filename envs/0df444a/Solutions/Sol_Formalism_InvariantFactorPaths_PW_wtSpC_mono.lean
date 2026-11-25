-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.wtSpC_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:41:04.368094+00:00
-- url     : https://prove2.me/submissions/0a4a635c-bbe1-4c15-807e-85b922b5284e

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_OrthogonalIsomorphismHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CommProjectionHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CompEqZeroOfNotDle

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
theorem _root_.solution (LL : Letters N) (j : ℕ) {Cs Cs' : Finset (Fin r)} (h : Cs ⊆ Cs') (la : Fin r → ℤ) :
    WtSpC p LL j Cs' la ≤ WtSpC p LL j Cs la := by
  intro x hx
  rw [WtSpC, MvPolynomial.mem_restrictSupport_iff] at hx ⊢
  exact fun m hm c hc => hx hm c (h hc)
end Formalism.InvariantFactorPaths.PW
