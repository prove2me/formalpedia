-- Prove2me | solution 1 for Formalism.L2.Th1.E.AnaSys.transC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:02:33.131471+00:00
-- url     : https://prove2.me/submissions/4c61765b-8fc6-46e0-a95c-1ec6135d3eea

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_IsogenyFormulaInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Bridge
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_BridgeTwoMore
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_AnaSys
import Theorems.Thm_Formalism_L2_Th1_E_AnaSys_flowC
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_Formalism_L2_Th1_A_expSpec
import Theorems.Thm_Formalism_L2_Th1_A_flowUniqueZ
import Theorems.Thm_Formalism_L2_Th1_A_plusFlow
import Theorems.Thm_Formalism_L2_Th1_A_plusZ
import Theorems.Thm_Formalism_L2_Th1_B_Ph_constantCoeff_psubst
import Theorems.Thm_Formalism_L2_Th1_F_TaylorSigmaUniqueness_constantCoeff_taylor0
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
open F.TaylorWp
variable (L : PeriodPair) (t : ℂ)
namespace Formalism.L2.Th1.E.AnaSys
theorem _root_.solution (ht : t ∉ L.lattice) :
    (A.xPlus (A.shortW L.g₂ L.g₃) (L.weierstrassP t) (L.derivWeierstrassP t / 2)).subst
        (A.expSer (A.shortW L.g₂ L.g₃)) = F.taylor0 fun z => L.weierstrassP (z + t) := by
  have heq : (A.shortW L.g₂ L.g₃).toAffine.Equation (L.weierstrassP t) (L.derivWeierstrassP t / 2) := by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [A.shortW]
    linear_combination (L.derivWeierstrassP_sq t ht) / 4
  have he0 : constantCoeff (A.expSer (A.shortW L.g₂ L.g₃)) = 0 := (A.expSpec ℂ _).1
  have hf := (A.plusFlow ℂ (A.shortW L.g₂ L.g₃) _ _ heq)
  refine (A.flowUniqueZ ℂ (A.shortW L.g₂ L.g₃) _ _ _ _ (A.plusZ ℂ _ _ _ heq).1 (flowC L t ht) ?_ ?_).1
  · rw [B.Ph.constantCoeff_psubst he0, hf.2.1, F.TaylorSigmaUniqueness.constantCoeff_taylor0, zero_add]
  · rw [B.Ph.constantCoeff_psubst he0, hf.2.2, map_mul, F.TaylorSigmaUniqueness.constantCoeff_taylor0, zero_add,
      constantCoeff_C]
    ring
end Formalism.L2.Th1.E.AnaSys
