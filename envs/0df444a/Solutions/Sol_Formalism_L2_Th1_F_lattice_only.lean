-- Prove2me | solution 1 for Formalism.L2.Th1.F.lattice_only
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:59:53.067425+00:00
-- url     : https://prove2.me/submissions/4043c2ec-7f48-48ea-a3a9-816f2fa3fdd8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_LatticeOnly
import Theorems.Thm_Formalism_L2_Th1_F_LatOnly_wZeta_eq
import Theorems.Thm_Formalism_L2_Th1_F_LatOnly_wSigma_eq
import Theorems.Thm_Formalism_L2_Th1_F_LatOnly_wp_eq
import Theorems.Thm_Formalism_L2_Th1_F_LatOnly_G_eq
import Theorems.Thm_Formalism_L2_Th1_F_LatOnly_wEta_eq
import Theorems.Thm_Formalism_L2_Th1_F_LatOnly_quasiPeriodConst_eq
import Theorems.Thm_Formalism_L2_Th1_F_LatOnly_area_eq
import Theorems.Thm_Formalism_L2_Th1_F_LatOnly_sgStar_eq
import Theorems.Thm_Formalism_L2_Th1_F_PeriodAreaSignLemmas_area_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
namespace Formalism.L2.Th1.F
theorem _root_.solution : LatticeOnly := by
  intro L L' h
  refine ⟨LatOnly.wZeta_eq h, LatOnly.wSigma_eq h, LatOnly.wEta_eq h, LatOnly.area_eq h,
    LatOnly.quasiPeriodConst_eq h, LatOnly.sgStar_eq h, LatOnly.wp_eq h, ?_, ?_⟩
  · first
      | simp only [PeriodPair.g₂, LatOnly.G_eq h]
      | (unfold PeriodPair.g₂
         rw [LatOnly.G_eq h])
      | (unfold PeriodPair.g₂
         done)
  · first
      | simp only [PeriodPair.g₃, LatOnly.G_eq h]
      | (unfold PeriodPair.g₃
         rw [LatOnly.G_eq h])
      | (unfold PeriodPair.g₃
         done)
end Formalism.L2.Th1.F
