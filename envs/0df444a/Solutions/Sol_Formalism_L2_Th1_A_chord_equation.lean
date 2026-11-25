-- Prove2me | solution 1 for Formalism.L2.Th1.A.chord_equation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:48:26.308019+00:00
-- url     : https://prove2.me/submissions/7e185334-d45f-4f13-b9ba-38c9f4feea8a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementN
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FglInvariant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_XPowSuccDvdOfDerivative
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_chord_rel
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
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Nn
namespace Formalism.L2.Th1.A
theorem _root_.solution : ChordEquation.{u} := by
  intro R _ W xP yP xQ yQ t hP hQ ht
  rw [WeierstrassCurve.Affine.equation_iff] at hP hQ
  have hL : (yP - yQ) * t * (xP - xQ) = yP - yQ := by linear_combination (yP - yQ) * ht
  obtain ⟨hc1, hc0⟩ := chord_rel hP hQ ht hL
  generalize (yP - yQ) * t = L at hL hc1 hc0 ⊢
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.addX]
  linear_combination -(L ^ 2 + W.a₁ * L - W.a₂ - xP - xQ) * hc1 - hc0
end Formalism.L2.Th1.A
