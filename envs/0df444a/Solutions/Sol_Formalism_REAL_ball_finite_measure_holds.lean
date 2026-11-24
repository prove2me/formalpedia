-- Prove2me | solution 1 for Formalism.REAL.ball_finite_measure_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:27:42.913244+00:00
-- url     : https://prove2.me/submissions/9ed53ff0-9be4-4e4e-9bd2-bc853f3c6c21

import Definitions.Def_Formalism_RealPlaceAnalysis_InstMeasurableSpaceUJ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_PlaceRankTwoOne
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Theorems.Thm_Formalism_REAL_hermitian_small_ball
import Theorems.Thm_Formalism_REAL_isClosedEmbeddingMatrix


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
theorem _root_.solution : BallFinite := by
  intro n ε R
  have hc : IsCompact {g : UJ ε | hsG g ≤ R} := by
    have := (isClosedEmbeddingMatrix n ε).1.isCompact_preimage ((hermitian_small_ball n ε).1 R)
    convert this using 1
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hsG]
    exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
  exact hc.measure_lt_top
end Formalism.REAL
