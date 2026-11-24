-- Prove2me | solution 1 for Formalism.L2.Th1.F.Homog.wSigma_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:36:47.814948+00:00
-- url     : https://prove2.me/submissions/1b8a85bd-bce0-4bb4-8b79-41d49adf3774

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_LatticeOnly
import Theorems.Thm_Formalism_L2_Th1_F_Homog_tprod_scale
import Theorems.Thm_Formalism_L2_Th1_F_Homog_wFactor_scale

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
open Formalism.L2.Th1.F.Homog
variable (L : PeriodPair) (c : ℂ) (hc : c ≠ 0)
namespace Formalism.L2.Th1.F.Homog
theorem _root_.solution (z : ℂ) : wSigma (scalePair L c hc) (c * z) = c * wSigma L z := by
  simp only [wSigma]
  rw [tprod_scale L c hc (fun w => wFactor w (c * z))]
  try dsimp only
  simp only [wFactor_scale c hc]
  ring
end Formalism.L2.Th1.F.Homog
