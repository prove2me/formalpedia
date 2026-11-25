-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.iSup_isoC_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:37:54.160798+00:00
-- url     : https://prove2.me/submissions/24cc2cff-1197-4983-ad57-3a7e60e5d663

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_OrthogonalIsomorphismHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CommProjectionHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CompEqZeroOfNotDle
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_isoC_congr

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
theorem _root_.solution (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    (⨆ (la' : Fin r → ℤ) (_ : la' ∈ {la' : Fin r → ℤ | ∀ c ∈ Cs, la' c = la c}), IsoC p LL j Cs la') =
      IsoC p LL j Cs la := by
  refine le_antisymm (iSup₂_le fun la' h => (isoC_congr LL j Cs h).le) ?_
  exact le_iSup₂_of_le la (fun c _ => rfl) le_rfl
end Formalism.InvariantFactorPaths.PW
