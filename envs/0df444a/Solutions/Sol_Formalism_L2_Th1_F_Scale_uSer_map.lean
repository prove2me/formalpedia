-- Prove2me | solution 1 for Formalism.L2.Th1.F.Scale.uSer_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:05:10.641206+00:00
-- url     : https://prove2.me/submissions/8b245d36-ca08-48aa-836a-67849e8c3104

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSig1S
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaScale
import Theorems.Thm_Formalism_L2_Th1_F_Scale_cc_wpDen
import Theorems.Thm_Formalism_L2_Th1_F_Scale_wpNum_map
import Theorems.Thm_Formalism_L2_Th1_F_Scale_wpDen_map
import Theorems.Thm_P2M_Formalism_L2_Th1_B_Map_map_inv__a3b389717e67


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism.L2.Th1.CM (cW wpNum wpDen uSer)
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Scale
open PowerSeries
variable {K K' : Type} [Field K] [Field K'] (φ : K →+* K')
namespace Formalism.L2.Th1.F.Scale
theorem _root_.solution [CharZero K] [CharZero K'] (g2 g3 : K) :
    map φ (uSer g2 g3) = uSer (φ g2) (φ g3) := by
  unfold uSer
  rw [map_mul, map_mul, map_X,
    Formalism.L2.Th1.B.Map.map_inv' φ (by rw [cc_wpDen]; exact one_ne_zero), wpNum_map, wpDen_map]
end Formalism.L2.Th1.F.Scale
