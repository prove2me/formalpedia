-- Prove2me | solution 1 for Formalism.L2.Th1.A.CurveSer.om_cc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:26:29.931827+00:00
-- url     : https://prove2.me/submissions/5d18b1a5-aebe-45e5-bbf2-118529602dff

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_fw_cc
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_fw_mul_om

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
namespace Formalism.L2.Th1.A.CurveSer
theorem _root_.solution : constantCoeff (om W) = 1 := by
  have h := congrArg constantCoeff (fw_mul_om W)
  rw [map_mul, fw_cc W, one_mul, map_one] at h
  exact h
end Formalism.L2.Th1.A.CurveSer
