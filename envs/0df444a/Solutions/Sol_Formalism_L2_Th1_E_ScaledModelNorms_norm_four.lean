-- Prove2me | solution 1 for Formalism.L2.Th1.E.ScaledModelNorms.norm_four
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:50:22.288891+00:00
-- url     : https://prove2.me/submissions/6fec1d5d-ff42-4e3a-8ad6-d3862fee58fa

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_CubeThreeR
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_CmIntegralityOfTorsionPoints
import Theorems.Thm_Formalism_L2_Th1_E_ScaledModelNorms_norm_nat
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.E.ScaledModelNorms
open Formalism.L2.Th1
variable (l : ℕ) [Fact l.Prime]
namespace Formalism.L2.Th1.E.ScaledModelNorms
theorem _root_.solution (hl : 5 ≤ l) : ‖(4 : ℂ_[l])‖ = 1 := by
  have h : ¬ l ∣ 4 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  simpa using norm_nat l h
end Formalism.L2.Th1.E.ScaledModelNorms
