-- Prove2me | solution 1 for Formalism.L2.Th1.E.TransGauss_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:52:55.825459+00:00
-- url     : https://prove2.me/submissions/f2da52e6-ecb9-4330-97b4-3edc8b497228

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ScaledXOffOrigin
import Theorems.Thm_Formalism_L2_Th1_E_Main_unitAt_C_mul_X
import Theorems.Thm_Formalism_L2_Th1_E_Main_unitAt_of_oneUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Main
set_option linter.unusedVariables false
namespace Formalism.L2.Th1.E
theorem _root_.solution (hR : IntRules) (hA : UnitAtRules) (hU : TransUnit) : TransGauss := by
  intro K _ _ _ W hW T _ π G hI hG t N hNn hNt
  obtain ⟨-, -, -, uG, -⟩ := hA K
  by_cases ht : π t = 0
  · obtain ⟨ε, hε, h⟩ := hG.1 t ht
    rw [h]
    exact uG 1 _ (unitAt_C_mul_X hε)
  · obtain ⟨h1, h2⟩ := hU K W hW T π G hI hG t N hNn hNt ht
    have h0 : constantCoeff (G t) ≠ 0 := hG.2.1 t ht
    have := uG 0 _ (unitAt_of_oneUnit h1 h2)
    rwa [← mul_assoc, ← map_mul, mul_inv_cancel₀ h0, map_one, one_mul] at this
end Formalism.L2.Th1.E
