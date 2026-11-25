-- Prove2me | solution 1 for Formalism.REAL.sqrt_frobenius_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:28:25.30554+00:00
-- url     : https://prove2.me/submissions/01ffa11f-3f6a-4934-b22e-18d36792911b

import Definitions.Def_Formalism_RealPlaceAnalysis_InstMeasurableSpaceUJ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_PlaceRankTwoOne
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Theorems.Thm_Formalism_REAL_sqrt_frobenius_eq_norm

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
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    Real.sqrt (hs (A * B)) ≤ Real.sqrt (hs A) * Real.sqrt (hs B) := by
  simp only [sqrt_frobenius_eq_norm]; exact Matrix.frobenius_norm_mul A B
end Formalism.REAL
