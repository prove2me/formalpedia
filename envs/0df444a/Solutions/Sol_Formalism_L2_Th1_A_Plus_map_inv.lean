-- Prove2me | solution 1 for Formalism.L2.Th1.A.Plus.map_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:00:08.595053+00:00
-- url     : https://prove2.me/submissions/08a34bd8-2295-4451-942a-558a5d0323e9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowTrans
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ToLTDenMulInv
import Theorems.Thm_Formalism_L2_Th1_A_Plus_tDen_mul_inv
import Theorems.Thm_Formalism_L2_Th1_A_Plus_map_tDen
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_one


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
variable {S : Type v} [CommRing S] (φ : R →+* S)
namespace Formalism.L2.Th1.A.Plus
theorem _root_.solution : PowerSeries.map φ (invOfUnit (tDen W xP) 1)
    = invOfUnit (tDen (W.map φ) (φ xP)) 1 := by
  have h1 : tDen (W.map φ) (φ xP) * PowerSeries.map φ (invOfUnit (tDen W xP) 1) = 1 := by
    rw [← Plus.map_tDen W xP φ, ← map_mul, tDen_mul_inv, map_one]
  have h2 := tDen_mul_inv (W.map φ) (φ xP)
  calc PowerSeries.map φ (invOfUnit (tDen W xP) 1)
      = (invOfUnit (tDen (W.map φ) (φ xP)) 1 * tDen (W.map φ) (φ xP))
          * PowerSeries.map φ (invOfUnit (tDen W xP) 1) := by
        rw [mul_comm (invOfUnit (tDen (W.map φ) (φ xP)) 1) (tDen (W.map φ) (φ xP)), h2, one_mul]
    _ = invOfUnit (tDen (W.map φ) (φ xP)) 1 := by rw [mul_assoc, h1, mul_one]
end Formalism.L2.Th1.A.Plus
