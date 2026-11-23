-- Prove2me | solution 1 for Formalism.L2.Th1.A.CurveSer.map_om
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:26:31.779216+00:00
-- url     : https://prove2.me/submissions/56291e8c-f065-4ab3-8de8-202cc9a2c389

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_map_invOfUnit
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_fw_cc
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_map_fw

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
theorem _root_.solution : PowerSeries.map φ (om W) = om (W.map φ) := by
  unfold om
  rw [map_invOfUnit φ (fw W) 1 (by rw [fw_cc W, Units.val_one]), map_fw W φ, map_one]
end Formalism.L2.Th1.A.CurveSer
