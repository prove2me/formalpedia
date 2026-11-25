-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RestrictedDualKernel.lemmaDKSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:35:22.03219+00:00
-- url     : https://prove2.me/submissions/e1b15bfd-6f5c-4591-b9bd-66c1f60a35a6

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictedDualKernel
import Theorems.Thm_Formalism_FourierDecayAlt_P_RestrictedDualKernel_cs_on
import Theorems.Thm_Formalism_FourierDecayAlt_P_RestrictedDualKernel_pos_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_DualKernelLemmas_dkDualOK
import Theorems.Thm_Formalism_FourierDecayAlt_P_DualKernelLemmas_dkStep1
import Theorems.Thm_Formalism_FourierDecayAlt_P_DualKernelLemmas_pair_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_DualKernelLemmas_real_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_act_csmul
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_act_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_dkStep4
import Theorems.Thm_Formalism_FourierDecayAlt_P_duality_list_holds
import Theorems.Thm_Formalism_FourierDecayAlt_P_kappa_formula_holds
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_GramProductIdentities_pair_act__bf313f925fd6


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
theorem _root_.solution : LemmaDKSub := by
  intro A S V _ _ _ _ _ _ _ _ _ _ ρ QQ q w L X D hS hD hDX hΦ hP
  have hok := dkDualOK S q w L hD
  have hdl := Formalism.FourierDecayAlt.P.duality_list_holds ℂ A S QQ q w L hS hD.2.1 hD.2.2.1 hok
  have hkap := Formalism.FourierDecayAlt.P.kappa_formula_holds ℂ S q w L hD.2.1 hD.2.2.1 hok
  have h4 := Formalism.FourierDecayAlt.P.GramProductIdentities.dkStep4 S q w L hD.1
  have hk0 : kap q w L ≠ 0 := hdl.2.1
  have hprod : (L.map fun l => qw q w l.pt).prod = kap q w L := by rw [hkap, h4]
  have hm : ∀ X₂, frm ρ (RRw QQ (L.map dl ++ w)) X₂ X₂ = kap q w L *
      frm ρ (RRw QQ (L ++ w)) (act (Ps QQ q w L) X₂) (act (Ps QQ q w L) X₂) := by
    intro X₂
    simp only [frm]
    rw [pair_act', ← act_mul, ← act_mul, hdl.2.2.2.1, act_csmul, pair_smul_left]
    field_simp
  refine ⟨fun X₁ h₁ X₂ h₂ => ?_, fun hq0 X₂ h₂ => ?_⟩
  · rw [hprod, hm, dkStep1 A S V ρ QQ q w L hS hD X₁ X₂]
    refine real_bound _ _ _ _ hk0 (hP X₁ h₁).2 (hP _ (hΦ X₂ h₂)).2 ?_
    exact cs_on ρ _ X hP h₁ (hΦ X₂ h₂)
  · rw [hprod] at hq0; rw [hm]; exact pos_mul hq0 (hP _ (hΦ X₂ h₂))
end Formalism.FourierDecayAlt.P.RestrictedDualKernel
