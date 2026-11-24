-- Prove2me | solution 1 for Formalism.L2.Th1.A.Plus.toL_tS_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:27:18.180174+00:00
-- url     : https://prove2.me/submissions/0ed32165-b169-4b63-b61c-0530b7f2bb34

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowTrans
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ToLTDenMulInv
import Theorems.Thm_Formalism_L2_Th1_A_Plus_toL_tDen_mul_inv
import Theorems.Thm_Formalism_L2_Th1_A_Plus_toL_X_mul
import Theorems.Thm_Formalism_L2_Th1_A_Plus_toL_tS
import Theorems.Thm_Formalism_L2_Th1_A_Plus_xL_sub

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
open Formalism.L2.Th1.A.Plus
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (xP yP : R)
namespace Formalism.L2.Th1.A.Plus
theorem _root_.solution : toL (tS W xP) * (xL W - HahnSeries.C xP) = 1 := by
  rw [xL_sub, toL_tS]
  calc (toL X : LaurentSeries R) ^ 2 * toL (invOfUnit (tDen W xP) 1) * (uPow (-1) ^ 2 * toL (tDen W xP))
      = ((toL X : LaurentSeries R) * uPow (-1)) ^ 2
          * (toL (tDen W xP) * toL (invOfUnit (tDen W xP) 1)) := by ring
    _ = 1 := by rw [toL_X_mul, toL_tDen_mul_inv, one_pow, one_mul]
end Formalism.L2.Th1.A.Plus
