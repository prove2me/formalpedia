-- Prove2me | solution 1 for Formalism.REAL.norm_sub_one_lt_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:45:20.048177+00:00
-- url     : https://prove2.me/submissions/ed6c2e34-cdc6-4009-8a89-7c42150afcf5

import Definitions.Def_Formalism_RealPlaceAnalysis_InstMeasurableSpaceUJ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_PlaceRankTwoOne
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Theorems.Thm_Formalism_REAL_frobenius_eq_norm_sq

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
theorem _root_.solution {n : ℕ} {u : Matrix (Fin n) (Fin n) ℂ} (hu : hs (u - 1) < 1 / 4) :
    ‖u - 1‖ < 1 / 2 := by
  rw [frobenius_eq_norm_sq] at hu
  nlinarith [norm_nonneg (u - 1)]
end Formalism.REAL
