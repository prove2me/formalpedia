-- Prove2me | solution 1 for Formalism.L2.Th1.E.AnaSys.prod_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:36:13.392867+00:00
-- url     : https://prove2.me/submissions/a5dbf239-ff6e-4505-9aaf-26f26ee45225

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_IsogenyFormulaInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Bridge
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_BridgeTwoMore
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_AnaSys
import Theorems.Thm_Formalism_L2_Th1_E_AnaSys_inU_congr
import Theorems.Thm_Formalism_L2_Th1_E_AnaSys_Rd_mul
import Theorems.Thm_Formalism_L2_Th1_E_AnaSys_Rd_add
import Theorems.Thm_Formalism_L2_Th1_E_AnaSys_Rd_const
import Theorems.Thm_Formalism_L2_Th1_E_AnaSys_cc_gT
import Theorems.Thm_Formalism_L2_Th1_E_AnaSys_px_ptOf
import Theorems.Thm_Formalism_L2_Th1_E_AnaSys_scaled_x_analytic_point
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_add
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_mul
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_key
import Theorems.Thm_Formalism_FG_InjVAux_Good_mul
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_add
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_mul
import Theorems.Thm_Formalism_FG_InvIntVAux_Low_add
import Theorems.Thm_Formalism_FG_InvIntVAux_Low_mul
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
import Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_CT_mul
import Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_Low_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_neg
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_one
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_pow
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_Formalism_L2_Th1_B_Jets_key
import Theorems.Thm_Formalism_L2_Th1_F_HalfPeriodDerivative_isOpen_compl
import Theorems.Thm_Formalism_L2_Th1_F_LegendreModelEllipticTorsion_key
import Theorems.Thm_Formalism_L2_Th1_F_PeriodLatticeBasisLemmas_isOpen_compl
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_add
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_const
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_mul
import Theorems.Thm_Formalism_L2_Th1_F_WeierstrassZetaQuasiPeriod_isOpen_compl
import Theorems.Thm_Formalism_L2_Th1_F_translateProduct
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
theorem _root_.solution (hT : TransWpBridge) (P Q : ℂ) (hQ : Q ∉ L.lattice) (hP : P ∉ L.lattice) :
    X ^ 2 * (gT l L ι (P + Q) * gT l L ι (P - Q)) =
      C (constantCoeff (gT l L ι Q) ^ 2) *
        (C (px (curveL l L ι) (ptOf l L ι Q)) * X ^ 2 - x2 (curveL l L ι) (ptOf l L ι P)) *
        gT l L ι P ^ 2 := by
  have hop : {z : ℂ | z + P ∉ L.lattice} ∈ nhds (0 : ℂ) :=
    (L.isClosed_lattice.isOpen_compl.preimage (continuous_add_const P)).mem_nhds (by simpa using hP)
  have hev : (fun z => F.opU L (P + Q) (F.sgStar L) z * F.opU L (P - Q) (F.sgStar L) z) =ᶠ[nhds 0]
      fun z => F.opU L Q (F.sgStar L) 0 ^ 2 * (L.weierstrassP Q + (-1) * L.weierstrassP (z + P)) *
        (F.opU L P (F.sgStar L) z * F.opU L P (F.sgStar L) z) := by
    filter_upwards [hop] with z hz
    rw [F.translateProduct L P Q z hQ hz]
    ring
  have hwp : Rd l L ι (fun z => L.weierstrassP (z + P)) (xT (curveL l L ι) (ptOf l L ι P)) := by
    refine ⟨?_, hT l L ι P hP⟩
    have h1 : AnalyticAt ℂ L.weierstrassP (0 + P) := L.analyticOnNhd_weierstrassP _ (by simpa using hP)
    exact AnalyticAt.fun_comp h1 (analyticAt_id.add analyticAt_const)
  have hl := ((Rd.opU l L ι (P + Q)).mul (Rd.opU l L ι (P - Q))).2
  have hr := (((Rd.const l L ι (F.opU L Q (F.sgStar L) 0 ^ 2)).mul
    ((Rd.const l L ι (L.weierstrassP Q)).add ((Rd.const l L ι (-1)).mul hwp))).mul
    ((Rd.opU l L ι P).mul (Rd.opU l L ι P))).2
  have key := hl.symm.trans ((inU_congr l L ι hev).trans hr)
  simp only [map_pow, map_neg, map_one] at key
  rw [cc_gT, px_ptOf l L ι Q hQ, scaled_x_analytic_point l L ι P hP]
  unfold gT
  simp only [map_pow]
  linear_combination (X ^ 2 * B.fExp (phL l L ι) ^ 2) * key
end Formalism.L2.Th1.E.AnaSys
