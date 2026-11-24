-- Prove2me | solution 1 for Formalism.REAL.norm_le_of_near_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:22:39.420341+00:00
-- url     : https://prove2.me/submissions/588d18d8-b9ed-46e2-a870-57825f1dd8e5

import Definitions.Def_Formalism_RealPlaceAnalysis_InstMeasurableSpaceUJ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_PlaceRankTwoOne
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Theorems.Thm_Formalism_REAL_norm_one_matrix_eq_sqrt
import Theorems.Thm_Formalism_REAL_norm_sub_one_lt_half

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
    ‖u‖ ≤ Real.sqrt n + 1 / 2 := by
  have h1 := norm_sub_one_lt_half hu
  have h2 : ‖u‖ ≤ ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ + ‖u - 1‖ := by
    calc ‖u‖ = ‖1 + (u - 1)‖ := by rw [add_sub_cancel]
      _ ≤ _ := norm_add_le _ _
  rw [norm_one_matrix_eq_sqrt] at h2
  linarith
end Formalism.REAL
