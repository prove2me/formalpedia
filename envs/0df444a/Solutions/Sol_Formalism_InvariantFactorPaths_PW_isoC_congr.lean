-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.isoC_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:55:20.852703+00:00
-- url     : https://prove2.me/submissions/22693e9a-400d-4f1a-adbc-3c6c5937c0bb

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_OrthogonalIsomorphismHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CommProjectionHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CompEqZeroOfNotDle
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_isoC_eq


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
theorem _root_.solution (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) {la la' : Fin r → ℤ}
    (h : ∀ c ∈ Cs, la c = la' c) : IsoC p LL j Cs la = IsoC p LL j Cs la' := by
  have hc : la ∘ enumC Cs = la' ∘ enumC Cs := by
    funext i
    exact h _ (Finset.orderEmbOfFin_mem Cs rfl i)
  rw [isoC_eq, isoC_eq, hc]
end Formalism.InvariantFactorPaths.PW
