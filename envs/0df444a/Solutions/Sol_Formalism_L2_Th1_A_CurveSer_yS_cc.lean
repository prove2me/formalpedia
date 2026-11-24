-- Prove2me | solution 1 for Formalism.L2.Th1.A.CurveSer.yS_cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:19:30.673281+00:00
-- url     : https://prove2.me/submissions/6e718882-f9ad-4b17-af81-1404be6bef8a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_xS_cc

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
theorem _root_.solution : constantCoeff (yS W) = -1 := by
  unfold yS
  rw [map_neg, xS_cc W]
end Formalism.L2.Th1.A.CurveSer
