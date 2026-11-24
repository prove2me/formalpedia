-- Prove2me | solution 1 for Formalism.L2.Th1.A.Plus.yL_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:44:13.783069+00:00
-- url     : https://prove2.me/submissions/21f3a396-35d3-47a9-8d66-30e6448850ca

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowTrans
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ToLTDenMulInv
import Theorems.Thm_Formalism_L2_Th1_A_Plus_toL_X_mul
import Theorems.Thm_Formalism_L2_Th1_A_Plus_yL_eq
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_pow
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_sub


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
theorem _root_.solution : yL W - HahnSeries.C yP = uPow (-1) ^ 3 * toL (yS W - C yP * X ^ 3) := by
  rw [yL_eq, map_sub, map_mul, map_pow, HahnSeries.ofPowerSeries_C, mul_sub]
  have h : (uPow (-1) : LaurentSeries R) ^ 3 * (HahnSeries.C yP * toL X ^ 3) = HahnSeries.C yP := by
    rw [mul_left_comm, ← mul_pow, mul_comm (uPow (-1) : LaurentSeries R) (toL X), toL_X_mul,
      one_pow, mul_one]
  rw [h]
end Formalism.L2.Th1.A.Plus
