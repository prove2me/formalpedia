-- Prove2me | solution 1 for Formalism.L2.Th1.A.CurveSer.map_iDen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:19:27.959455+00:00
-- url     : https://prove2.me/submissions/4a5c95c4-c708-4cce-9a8f-f63f51b940e8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_map_wSer

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
theorem _root_.solution : PowerSeries.map φ (iDen W) = iDen (W.map φ) := by
  unfold iDen
  simp [map_wSer W φ]
end Formalism.L2.Th1.A.CurveSer
