-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DualKernelLemmas.lemmaDK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:26:21.488771+00:00
-- url     : https://prove2.me/submissions/fde4d347-6a70-4d14-84a4-a517b4e4ff7a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialFlipCommuteDiagScalarOfFree
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
import Theorems.Thm_Formalism_FourierDecayAlt_P_DualKernelLemmas_pair_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_DualKernelLemmas_real_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_DualKernelLemmas_dkDualOK
import Theorems.Thm_Formalism_FourierDecayAlt_P_DualKernelLemmas_dkStep1
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_act_csmul
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_act_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_csPos
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DualKernelLemmas
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities
open scoped Matrix
namespace Formalism.FourierDecayAlt.P.DualKernelLemmas
theorem _root_.solution : LemmaDK := by
  intro A S V _ _ _ _ _ _ _ _ _ _ ρ QQ q w L hS hD hP X₁ X₂
  have hok := dkDualOK S q w L hD
  have hdl := Formalism.FourierDecayAlt.P.duality_list_holds ℂ A S QQ q w L hS hD.2.1 hD.2.2.1 hok
  have hkap := Formalism.FourierDecayAlt.P.kappa_formula_holds ℂ S q w L hD.2.1 hD.2.2.1 hok
  have h4 := Formalism.FourierDecayAlt.P.GramProductIdentities.dkStep4 S q w L hD.1
  have hk0 : kap q w L ≠ 0 := hdl.2.1
  have hprod : (L.map fun l => qw q w l.pt).prod = kap q w L := by rw [hkap, h4]
  have h1 := dkStep1 A S V ρ QQ q w L hS hD X₁ X₂
  have hm : frm ρ (RRw QQ (L.map dl ++ w)) X₂ X₂ = kap q w L *
      frm ρ (RRw QQ (L ++ w)) (act (Ps QQ q w L) X₂) (act (Ps QQ q w L) X₂) := by
    simp only [frm]
    rw [pair_act', ← act_mul, ← act_mul, hdl.2.2.2.1, act_csmul, pair_smul_left]
    field_simp
  rw [hprod, hm, h1]
  refine real_bound _ _ _ _ hk0 (hP X₁).2 (hP _).2 ?_
  exact csPos A S V ρ _ X₁ _ hP
end Formalism.FourierDecayAlt.P.DualKernelLemmas
