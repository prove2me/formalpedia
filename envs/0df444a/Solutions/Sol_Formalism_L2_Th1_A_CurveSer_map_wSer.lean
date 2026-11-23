-- Prove2me | solution 1 for Formalism.L2.Th1.A.CurveSer.map_wSer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:16.768408+00:00
-- url     : https://prove2.me/submissions/65179a70-e3d1-498e-97a3-7a141165a975

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_wSer_fixed
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_wSer_unique
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_wSer_cc

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
theorem _root_.solution : PowerSeries.map φ (wSer W) = wSer (W.map φ) := by
  refine wSer_unique (W.map φ) ?_
  unfold Formalism.ELL.WFixed
  refine ⟨?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      wSer_cc W, map_zero]
  · conv_lhs => rw [(wSer_fixed W).2]
    simp
end Formalism.L2.Th1.A.CurveSer
