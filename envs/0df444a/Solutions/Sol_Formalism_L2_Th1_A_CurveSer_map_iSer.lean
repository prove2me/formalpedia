-- Prove2me | solution 1 for Formalism.L2.Th1.A.CurveSer.map_iSer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:29:32.177125+00:00
-- url     : https://prove2.me/submissions/5d085f20-eb7a-4738-a78e-e78343b9bef2

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_map_invOfUnit
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_iDen_cc
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_map_iDen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.CurveSer
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable {S : Type v} [CommRing S] (φ : R →+* S)
namespace Formalism.L2.Th1.A.CurveSer
theorem _root_.solution : PowerSeries.map φ (iSer W) = iSer (W.map φ) := by
  have hu : Units.map (φ : R →* S) (-1) = -1 := Units.ext (by simp)
  unfold iSer
  rw [map_mul, map_X, map_invOfUnit φ (iDen W) (-1) (by rw [iDen_cc W, Units.val_neg, Units.val_one]),
    map_iDen W φ, hu]
end Formalism.L2.Th1.A.CurveSer
