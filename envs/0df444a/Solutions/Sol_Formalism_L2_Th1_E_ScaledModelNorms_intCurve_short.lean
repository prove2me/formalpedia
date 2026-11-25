-- Prove2me | solution 1 for Formalism.L2.Th1.E.ScaledModelNorms.intCurve_short
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:25:22.266009+00:00
-- url     : https://prove2.me/submissions/4c0c3630-4501-43d1-b760-0c15b8d35a8c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_CubeThreeR
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_CmIntegralityOfTorsionPoints
import Theorems.Thm_Formalism_L2_Th1_E_ScaledModelNorms_norm_four
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
theorem _root_.solution (hl : 5 ≤ l) (g2 g3 : ℂ_[l]) (h2 : ‖g2‖ ≤ 1) (h3 : ‖g3‖ ≤ 1)
    (hD : ‖g2 ^ 3 - 27 * g3 ^ 2‖ = 1) : IntCurve (A.shortW g2 g3) := by
  have hΔ : (A.shortW g2 g3).Δ = g2 ^ 3 - 27 * g3 ^ 2 := by
    simp only [A.shortW, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [A.shortW]
  · simp [A.shortW]
  · simp [A.shortW]
  · show ‖-g2 / 4‖ ≤ 1
    rw [norm_div, norm_neg, norm_four l hl, div_one]; exact h2
  · show ‖-g3 / 4‖ ≤ 1
    rw [norm_div, norm_neg, norm_four l hl, div_one]; exact h3
  · rw [hΔ]; exact hD
end Formalism.L2.Th1.E.ScaledModelNorms
