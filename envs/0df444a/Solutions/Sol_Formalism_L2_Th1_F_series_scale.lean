-- Prove2me | solution 1 for Formalism.L2.Th1.F.series_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:13:19.329+00:00
-- url     : https://prove2.me/submissions/36896538-62e5-443f-975b-585532ea574e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSig1S
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaScale
import Theorems.Thm_Formalism_L2_Th1_F_Scale_cW_scale
import Theorems.Thm_Formalism_L2_Th1_F_Scale_wpNum_scale
import Theorems.Thm_Formalism_L2_Th1_F_Scale_wpDen_scale
import Theorems.Thm_Formalism_L2_Th1_F_Scale_pOf_scale
import Theorems.Thm_Formalism_L2_Th1_F_Scale_uSer_scale

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
theorem _root_.solution : SeriesScale := fun _ _ _ g2 g3 lam =>
  ⟨Scale.cW_scale g2 g3 lam, Scale.wpNum_scale g2 g3 lam, Scale.wpDen_scale g2 g3 lam,
    Scale.pOf_scale g2 g3 lam, Scale.uSer_scale g2 g3 lam⟩
end Formalism.L2.Th1.F
