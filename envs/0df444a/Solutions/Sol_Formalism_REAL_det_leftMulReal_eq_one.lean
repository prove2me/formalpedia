-- Prove2me | solution 1 for Formalism.REAL.det_leftMulReal_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:23:46.075435+00:00
-- url     : https://prove2.me/submissions/e2e8da34-c290-424c-a5fe-d79c57ebd371

import Definitions.Def_Formalism_RealPlaceAnalysis_InstMeasurableSpaceUJ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_PlaceRankTwoOne
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Theorems.Thm_Formalism_REAL_det_leftMul_restrictScalars
import Theorems.Thm_Formalism_REAL_normSq_det_indefinite_unitary

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
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    LinearMap.det (leftMulReal g) = 1 := by
  unfold leftMulReal
  have := LinearMap.det_conj ((LinearMap.mulLeft ℂ g).restrictScalars ℝ)
    (matrixCoordinatesEquiv n).symm
  rw [LinearEquiv.symm_symm] at this
  rw [this, det_leftMul_restrictScalars, normSq_det_indefinite_unitary hg, one_pow]
end Formalism.REAL
