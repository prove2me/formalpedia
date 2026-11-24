-- Prove2me | solution 1 for Formalism.L2.Th1.F.series_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:15:42.523262+00:00
-- url     : https://prove2.me/submissions/bb2c7667-e3e4-43e8-88cf-8909b86422e0

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSig1S
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaScale
import Theorems.Thm_Formalism_L2_Th1_F_Scale_wpNum_map
import Theorems.Thm_Formalism_L2_Th1_F_Scale_wpDen_map
import Theorems.Thm_Formalism_L2_Th1_F_Scale_pOf_map
import Theorems.Thm_Formalism_L2_Th1_F_Scale_uSer_map
import Theorems.Thm_Formalism_L2_Th1_B_Map_map_sgStar
import Theorems.Thm_Formalism_L2_Th1_B_Map_map_sigma


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
namespace Formalism.L2.Th1.F
theorem _root_.solution : SeriesMap := fun _ _ _ _ _ _ φ g2 g3 s P =>
  ⟨Scale.wpNum_map φ g2 g3, Scale.wpDen_map φ g2 g3, Scale.pOf_map φ g2 g3,
    Scale.uSer_map φ g2 g3, Formalism.L2.Th1.B.Map.map_sigma φ P, Formalism.L2.Th1.B.Map.map_sgStar φ s P⟩
end Formalism.L2.Th1.F
