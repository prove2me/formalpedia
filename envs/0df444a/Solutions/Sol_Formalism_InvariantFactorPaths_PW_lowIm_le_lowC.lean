-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.lowIm_le_lowC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:41:37.286799+00:00
-- url     : https://prove2.me/submissions/461348b4-5b1a-4e49-b247-a9799be8a399

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
theorem _root_.solution (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) :
    lowIm (GAe p LL j (enumC Cs)) ≤ lowC p LL j Cs := by
  unfold lowIm lowC
  refine iSup₂_le fun a b => iSup_le fun hab => ?_
  exact le_iSup₂_of_le (enumC Cs a) (enumC Cs b)
    (le_iSup_of_le ⟨Finset.orderEmbOfFin_mem Cs rfl a, Finset.orderEmbOfFin_mem Cs rfl b,
      (enumC Cs).strictMono hab⟩ le_rfl)
end Formalism.InvariantFactorPaths.PW
