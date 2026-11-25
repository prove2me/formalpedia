-- Prove2me | solution 1 for Formalism.REAL.of_leftMulReal_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:21:38.450666+00:00
-- url     : https://prove2.me/submissions/82aa202b-a831-439d-8e1f-a72c279960cb

import Definitions.Def_Formalism_RealPlaceAnalysis_InstMeasurableSpaceUJ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_PlaceRankTwoOne
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Theorems.Thm_Formalism_REAL_leftMulReal_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology Metric Kronecker
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : MatrixCoordinates n) :
    Matrix.of (leftMulReal A x) = A * Matrix.of x := by
  rw [leftMulReal_apply, Equiv.apply_symm_apply]
end Formalism.REAL
