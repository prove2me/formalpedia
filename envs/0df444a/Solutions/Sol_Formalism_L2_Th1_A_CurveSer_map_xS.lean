-- Prove2me | solution 1 for Formalism.L2.Th1.A.CurveSer.map_xS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:27:06.684851+00:00
-- url     : https://prove2.me/submissions/a281cf18-7173-46ad-8a58-e5e4e2889192

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_map_invOfUnit
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_wU_cc
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_map_wU
import Theorems.Thm_Formalism_ELL_CubeThreeAlt_wU_cc
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_wU_cc


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
theorem _root_.solution : PowerSeries.map φ (xS W) = xS (W.map φ) := by
  unfold xS
  rw [map_invOfUnit φ (wU W) 1 (by rw [wU_cc W, Units.val_one]), map_wU W φ, map_one]
end Formalism.L2.Th1.A.CurveSer
