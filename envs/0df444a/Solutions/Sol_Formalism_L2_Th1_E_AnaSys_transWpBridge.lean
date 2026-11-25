-- Prove2me | solution 1 for Formalism.L2.Th1.E.AnaSys.transWpBridge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:18:11.082469+00:00
-- url     : https://prove2.me/submissions/71c299d4-adf3-4a3a-bbee-e294c05afed7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_IsogenyFormulaInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Bridge
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_BridgeTwoMore
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_AnaSys
import Theorems.Thm_Formalism_L2_Th1_E_AnaSys_lgS
import Theorems.Thm_Formalism_L2_Th1_E_AnaSys_ptOf_notMem
import Theorems.Thm_Formalism_L2_Th1_E_AnaSys_curveL_eq
import Theorems.Thm_Formalism_L2_Th1_E_AnaSys_transC
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_ofNat
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_Formalism_L2_Th1_A_expSpec
import Theorems.Thm_Formalism_L2_Th1_A_plusMap
import Theorems.Thm_Formalism_L2_Th1_A_zMap
import Theorems.Thm_Formalism_L2_Th1_B_Ph_hs
import Theorems.Thm_P2M_Formalism_L2_Th1_B_Map_map_psubst__d587dd5fe1df
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
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.E.AnaSys
open Formalism.L2.Th1
variable (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
variable {l L ι}
variable (l L ι)
namespace Formalism.L2.Th1.E.AnaSys
theorem _root_.solution : TransWpBridge := by
  intro l _ L ι t ht
  have hz := A.zMap ℂ ℂ_[l] (ι : ℂ →+* ℂ_[l]) (A.shortW L.g₂ L.g₃)
  have hp := (A.plusMap ℂ ℂ_[l] (ι : ℂ →+* ℂ_[l]) (A.shortW L.g₂ L.g₃) (L.weierstrassP t)
    (L.derivWeierstrassP t / 2)).2.1
  have he := A.expSpec ℂ_[l] (curveL l L ι)
  unfold inU
  rw [← transC L t ht, B.Map.map_psubst' _ (A.expSpec ℂ _).1, hz.2.1, hp, ← curveL_eq,
    subst_comp_subst_apply (B.Ph.hs he.1) (lgS l L ι), he.2.2.2.1, X_subst, ptOf_notMem l L ι t ht]
  simp only [xT, px, py, RingEquiv.coe_toRingHom, map_div₀, map_ofNat]
end Formalism.L2.Th1.E.AnaSys
