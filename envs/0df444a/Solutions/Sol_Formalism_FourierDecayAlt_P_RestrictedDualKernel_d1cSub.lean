-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RestrictedDualKernel.d1cSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:51:57.146194+00:00
-- url     : https://prove2.me/submissions/e4808372-2bc6-422d-af88-b7273601772c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictedDualKernel
import Theorems.Thm_Formalism_FourierDecayAlt_P_RestrictedDualKernel_cs_on
import Theorems.Thm_Formalism_FourierDecayAlt_P_RestrictedDualKernel_pos_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_DualKernelLemmas_d1a
import Theorems.Thm_Formalism_FourierDecayAlt_P_DualKernelLemmas_d1b
import Theorems.Thm_Formalism_FourierDecayAlt_P_DualKernelLemmas_real_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RestrictedDualKernel
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.DualKernelLemmas
open scoped Matrix ComplexOrder
namespace Formalism.FourierDecayAlt.P.RestrictedDualKernel
theorem _root_.solution : DualityPositiveSubspace := by
  intro A S V _ _ _ _ _ _ _ _ _ _ ρ Ω RR TT q a Y X D hD hDX hΦ hP
  have hq : q Y ≠ 0 := hD.2.2.2.2.2
  have hm : ∀ X₂, frm ρ (RR * ins a (TT (↑Y + 1))ᵀ) X₂ X₂ =
      q Y * frm ρ (RR * ins a (TT ↑Y)) (act (PsiP TT q a ↑Y) X₂) (act (PsiP TT q a ↑Y) X₂) := by
    intro X₂
    rw [d1b A S V ρ Ω RR TT q a Y hD X₂ X₂]; field_simp
  refine ⟨fun X₁ h₁ X₂ h₂ => ?_, fun hq0 X₂ h₂ => ?_⟩
  · rw [hm, d1a A S V ρ Ω RR TT q a Y hD X₁ X₂]
    refine real_bound _ _ _ _ hq (hP X₁ h₁).2 (hP _ (hΦ X₂ h₂)).2 ?_
    exact cs_on ρ _ X hP h₁ (hΦ X₂ h₂)
  · rw [hm]; exact pos_mul hq0 (hP _ (hΦ X₂ h₂))
end Formalism.FourierDecayAlt.P.RestrictedDualKernel
