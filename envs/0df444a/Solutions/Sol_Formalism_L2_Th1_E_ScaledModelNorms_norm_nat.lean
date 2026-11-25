-- Prove2me | solution 1 for Formalism.L2.Th1.E.ScaledModelNorms.norm_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:40:44.175334+00:00
-- url     : https://prove2.me/submissions/7ee27f41-1bd9-448e-b81a-2d12bc90650b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_CubeThreeR
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_CmIntegralityOfTorsionPoints
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
theorem _root_.solution {N : ℕ} (h : ¬ l ∣ N) : ‖(N : ℂ_[l])‖ = 1 := by
  have hp : l.Prime := Fact.out
  have e : (N : ℂ_[l]) = ((algebraMap ℚ_[l] (PadicAlgCl l) (N : ℚ_[l]) : PadicAlgCl l) : ℂ_[l]) := by
    simp
  rw [e, PadicComplex.norm_extends', Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd hp).2 h
end Formalism.L2.Th1.E.ScaledModelNorms
