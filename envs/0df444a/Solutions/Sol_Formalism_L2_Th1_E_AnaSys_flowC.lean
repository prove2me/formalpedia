-- Prove2me | solution 1 for Formalism.L2.Th1.E.AnaSys.flowC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:36:09.826617+00:00
-- url     : https://prove2.me/submissions/fca9d096-fedc-4f89-92fe-e3282d48e6c2

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_IsogenyFormulaInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Bridge
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_BridgeTwoMore
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_AnaSys
import Theorems.Thm_Formalism_L2_Th1_E_AnaSys_Rd_mul
import Theorems.Thm_Formalism_L2_Th1_E_AnaSys_Rd_add
import Theorems.Thm_Formalism_L2_Th1_E_AnaSys_Rd_const
import Theorems.Thm_Formalism_L2_Th1_E_AnaSys_ev_notMem
import Theorems.Thm_Formalism_L2_Th1_E_AnaSys_T_wp
import Theorems.Thm_Formalism_L2_Th1_E_AnaSys_T_dwp
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_add
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_mul
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_pow
import Theorems.Thm_Formalism_FG_InjVAux_Good_mul
import Theorems.Thm_Formalism_FG_InjVAux_Good_pow
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_add
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_mul
import Theorems.Thm_Formalism_FG_InvIntVAux_Low_add
import Theorems.Thm_Formalism_FG_InvIntVAux_Low_mul
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
import Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_CT_mul
import Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_CT_pow
import Theorems.Thm_Formalism_HermitianLattices_ExpSeriesBivariate_ExpSeriesAddition_Low_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_ofNat
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_T_congr
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_ev_notMem
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_add
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_const
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_mul
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_pow
import Theorems.Thm_Formalism_L2_Th1_F_Taylor_taylor0_congr
import Theorems.Thm_Formalism_L2_Th1_F_Taylor_taylor0_deriv
import Theorems.Thm_Formalism_L2_Th1_F_pSecond
import Theorems.Thm_Formalism_L2_Th1_F_taylorRing
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
    A.IsFlow (A.curveS (A.shortW L.g₂ L.g₃)) (derivative ℂ)
      (F.taylor0 fun z => L.weierstrassP (z + t))
      (C (1 / 2 : ℂ) * F.taylor0 fun z => L.derivWeierstrassP (z + t)) := by
  have hr := F.taylorRing
  have hp := T_wp L t ht
  have hq := T_dwp L t ht
  have e1 : (F.taylor0 fun z => L.derivWeierstrassP (z + t)) *
        (F.taylor0 fun z => L.derivWeierstrassP (z + t)) =
      C (4 : ℂ) * (F.taylor0 fun z => L.weierstrassP (z + t)) ^ 3 +
        (C (-L.g₂) * (F.taylor0 fun z => L.weierstrassP (z + t)) + C (-L.g₃)) := by
    rw [← (T.mul hr hq hq).2, ← (T.add hr (T.mul hr (T.const hr 4) (T.pow hr hp 3))
      (T.add hr (T.mul hr (T.const hr (-L.g₂)) hp) (T.const hr (-L.g₃)))).2]
    apply F.Taylor.taylor0_congr
    filter_upwards [ev_notMem L t ht] with z hz
    have := L.derivWeierstrassP_sq (z + t) hz
    linear_combination this
  have e2 : derivative ℂ (F.taylor0 fun z => L.weierstrassP (z + t)) =
      F.taylor0 fun z => L.derivWeierstrassP (z + t) := by
    rw [← F.Taylor.taylor0_deriv]
    congr 1
    funext z
    rw [deriv_comp_add_const, L.deriv_weierstrassP]
  have e3 : derivative ℂ (F.taylor0 fun z => L.derivWeierstrassP (z + t)) =
      C (6 : ℂ) * (F.taylor0 fun z => L.weierstrassP (z + t)) ^ 2 + C (-(L.g₂ / 2)) := by
    rw [← F.Taylor.taylor0_deriv, ← (T.add hr (T.mul hr (T.const hr 6) (T.pow hr hp 2))
      (T.const hr (-(L.g₂ / 2)))).2]
    apply F.Taylor.taylor0_congr
    filter_upwards [ev_notMem L t ht] with z hz
    rw [deriv_comp_add_const, (F.pSecond L (z + t) hz).deriv]
    ring
  have c2 : (C (1 / 2 : ℂ) : PowerSeries ℂ) * 2 = 1 := by
    rw [← map_ofNat (C : ℂ →+* PowerSeries ℂ) 2, ← map_mul]; norm_num
  have k2 : (C (-L.g₂ / 4) : PowerSeries ℂ) = C (1 / 2 : ℂ) * C (1 / 2 : ℂ) * C (-L.g₂) := by
    rw [← map_mul, ← map_mul]; congr 1; ring
  have k3 : (C (-L.g₃ / 4) : PowerSeries ℂ) = C (1 / 2 : ℂ) * C (1 / 2 : ℂ) * C (-L.g₃) := by
    rw [← map_mul, ← map_mul]; congr 1; ring
  have k4 : (C (-(L.g₂ / 2)) : PowerSeries ℂ) = C (1 / 2 : ℂ) * C (-L.g₂) := by
    rw [← map_mul]; congr 1; ring
  have c4 : (C (4 : ℂ) : PowerSeries ℂ) = 4 := map_ofNat C 4
  have c6 : (C (6 : ℂ) : PowerSeries ℂ) = 6 := map_ofNat C 6
  refine ⟨?_, ?_, ?_⟩
  · rw [WeierstrassCurve.Affine.equation_iff]
    simp only [A.shortW, WeierstrassCurve.map, map_zero]
    rw [k2, k3]
    rw [c4] at e1
    linear_combination (C (1 / 2 : ℂ) * C (1 / 2 : ℂ)) * e1 +
      ((F.taylor0 fun z => L.weierstrassP (z + t)) ^ 3 * (C (1 / 2 : ℂ) * 2 + 1)) * c2
  · simp only [A.shortW, WeierstrassCurve.map, map_zero]
    linear_combination e2 - (F.taylor0 fun z => L.derivWeierstrassP (z + t)) * c2
  · simp only [A.shortW, WeierstrassCurve.map, map_zero]
    rw [Derivation.leibniz, derivative_C, smul_zero, add_zero, smul_eq_mul, e3, k2, k4, c6]
    linear_combination (3 * (F.taylor0 fun z => L.weierstrassP (z + t)) ^ 2) * c2
end Formalism.L2.Th1.E.AnaSys
