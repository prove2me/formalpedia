-- Prove2me | solution 1 for Formalism.L2.Th1.B.SAdd.sigma_addition_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:48:54.975654+00:00
-- url     : https://prove2.me/submissions/6a3a05cd-0c25-464b-9853-74c3532fb0b3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementE
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffQuotientXSq
import Theorems.Thm_Formalism_L2_Th1_B_SAdd_constantCoeff_dz_sW
import Theorems.Thm_Formalism_L2_Th1_B_SAdd_sigma_rules_hold
import Theorems.Thm_Formalism_L2_Th1_B_SAdd_shear_two_variables_holds
import Theorems.Thm_Formalism_L2_Th1_B_SAdd_eval_second_zero_one
import Theorems.Thm_Formalism_L2_Th1_B_SAdd_shear_alg
import Theorems.Thm_Formalism_L2_Th1_B_Add0_partialDeriv_inVar_self
import Theorems.Thm_Formalism_L2_Th1_B_Add0_triple_lintegral_eq
import Theorems.Thm_Formalism_L2_Th1_B_Add1_constantCoeff_inVar_eq_zero
import Theorems.Thm_Formalism_L2_Th1_B_Add1_inVarAlgHom_C
import Theorems.Thm_Formalism_L2_Th1_B_Add1_partialDeriv_inVar_self
import Theorems.Thm_Formalism_L2_Th1_B_Add1_pd_mul
import Theorems.Thm_Formalism_L2_Th1_B_Add1_pd_sub
import Theorems.Thm_Formalism_L2_Th1_B_Add1_restrictSecondZero_inVar_one
import Theorems.Thm_Formalism_L2_Th1_B_Add1_triple_lintegral_eq
import Theorems.Thm_Formalism_L2_Th1_B_evalYZero_add
import Theorems.Thm_Formalism_L2_Th1_B_evalYZero_mul
import Theorems.Thm_Formalism_L2_Th1_B_eval_second_zero_at_variable_zero
import Theorems.Thm_Formalism_L2_Th1_B_eval_second_zero_sub
import Theorems.Thm_Formalism_L2_Th1_B_partialDeriv_inVar_self
import Theorems.Thm_Formalism_L2_Th1_B_pderiv_at_variable_of_ne
import Theorems.Thm_Formalism_L2_Th1_B_restrictSecondZero_inVar_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.SAdd
open Formalism.InvariantFactorPaths.G7 (at1)
namespace Formalism.L2.Th1.B.SAdd
theorem _root_.solution : SAdd := by
  intro K _ _ A kap w hw
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := sigma_rules_hold K A kap w hw
  obtain ⟨hw0, hw2, -⟩ := hw
  have E1 : ∀ i : Fin 2, at1 i w = at1 i (sW w) ^ 2 := by
    intro i
    have := congrArg (at1 i) h1
    simpa only [Add1.triple_lintegral_eq, map_pow] using this.symm
  have E4 : ∀ i : Fin 2, at1 i (dz w) = 2 * at1 i (sW w) * at1 i (dz (sW w)) := by
    intro i
    have := congrArg (at1 i) h4
    simpa only [Add1.triple_lintegral_eq, map_mul, map_ofNat] using this.symm
  have E5 : ∀ i : Fin 2, at1 i (dz (sW w)) ^ 2 =
      1 + MvPowerSeries.C A * at1 i (sW w) ^ 2 + MvPowerSeries.C kap * (at1 i (sW w) ^ 2) ^ 2 := by
    intro i
    have := congrArg (at1 i) h5
    rw [← E1]
    simpa only [Add1.triple_lintegral_eq, map_pow, map_add, map_mul, map_one, Add1.inVarAlgHom_C] using this
  have E6 : ∀ i : Fin 2, at1 i (dz (dz (sW w))) =
      (MvPowerSeries.C A + 2 * MvPowerSeries.C kap * at1 i (sW w) ^ 2) * at1 i (sW w) := by
    intro i
    have := congrArg (at1 i) h6
    rw [← E1]
    simpa only [Add1.triple_lintegral_eq, map_add, map_mul, map_ofNat, Add1.inVarAlgHom_C] using this
  set d : MvPowerSeries (Fin 2) K := 1 - MvPowerSeries.C kap * at1 0 w * at1 1 w with hd
  set n : MvPowerSeries (Fin 2) K :=
    at1 0 (sW w) * at1 1 (dz (sW w)) + at1 1 (sW w) * at1 0 (dz (sW w)) with hn
  have hd0 : MvPowerSeries.constantCoeff d = 1 := by
    rw [hd, map_sub, map_mul, Add1.constantCoeff_inVar_eq_zero 1 hw0, mul_zero, map_one, sub_zero]
  have hdne : d ≠ 0 := by
    intro h
    rw [h, map_zero] at hd0
    exact zero_ne_one hd0
  have hdi : d⁻¹ * d = 1 := MvPowerSeries.inv_mul_cancel d (by rw [hd0]; exact one_ne_zero)
  have hhd : n * d⁻¹ * d = n := by rw [mul_assoc, hdi, mul_one]
  have n01 : (1 : Fin 2) ≠ 0 := by decide
  have n10 : (0 : Fin 2) ≠ 1 := by decide
  have pn0 : pd 0 n = at1 1 (dz (sW w)) * at1 0 (dz (sW w)) +
      at1 1 (sW w) * at1 0 (dz (dz (sW w))) := by
    rw [hn, pd, map_add]
    change pd 0 _ + pd 0 _ = _
    rw [Add1.pd_mul, Add1.pd_mul, partialDeriv_inVar_self, partialDeriv_inVar_self, pderiv_at_variable_of_ne n01, pderiv_at_variable_of_ne n01]
    ring
  have pn1 : pd 1 n = at1 0 (sW w) * at1 1 (dz (dz (sW w))) +
      at1 0 (dz (sW w)) * at1 1 (dz (sW w)) := by
    rw [hn, pd, map_add]
    change pd 1 _ + pd 1 _ = _
    rw [Add1.pd_mul, Add1.pd_mul, partialDeriv_inVar_self, partialDeriv_inVar_self, pderiv_at_variable_of_ne n10, pderiv_at_variable_of_ne n10]
    ring
  have pC : ∀ i : Fin 2, pd i (MvPowerSeries.C kap : MvPowerSeries (Fin 2) K) = 0 :=
    fun i => MvPowerSeries.pderiv_C
  have p1 : ∀ i : Fin 2, pd i (1 : MvPowerSeries (Fin 2) K) = 0 :=
    fun i => MvPowerSeries.pderiv_one
  have pd0 : pd 0 d = -(MvPowerSeries.C kap * at1 0 (dz w) * at1 1 w) := by
    rw [hd, Add1.pd_sub, Add1.pd_mul, Add1.pd_mul, p1, pC, partialDeriv_inVar_self, pderiv_at_variable_of_ne n01]
    ring
  have pd1 : pd 1 d = -(MvPowerSeries.C kap * at1 0 w * at1 1 (dz w)) := by
    rw [hd, Add1.pd_sub, Add1.pd_mul, Add1.pd_mul, p1, pC, partialDeriv_inVar_self, pderiv_at_variable_of_ne n10]
    ring
  have halg : d * (pd 0 n - pd 1 n) = n * (pd 0 d - pd 1 d) := by
    have := shear_alg (MvPowerSeries.C kap) (MvPowerSeries.C A) (at1 0 (sW w)) (at1 1 (sW w))
      (at1 0 (dz (sW w))) (at1 1 (dz (sW w))) (E5 0) (E5 1)
    rw [pn0, pn1, pd0, pd1, hd, hn, E6, E6, E4, E4, E1, E1]
    linear_combination this
  have q0 := congrArg (pd 0) hhd
  have q1 := congrArg (pd 1) hhd
  rw [Add1.pd_mul] at q0 q1
  have hsh : pd 0 (n * d⁻¹) = pd 1 (n * d⁻¹) := by
    refine sub_eq_zero.mp ?_
    refine (mul_eq_zero.mp (?_ : (d * d) * (pd 0 (n * d⁻¹) - pd 1 (n * d⁻¹)) = 0)).resolve_left
      (mul_ne_zero hdne hdne)
    linear_combination d * q0 - d * q1 + halg - (pd 0 d - pd 1 d) * hhd
  have hS := shear_two_variables_holds K (n * d⁻¹) hsh
  have hev : ev0 (n * d⁻¹) = sW w := by
    have e := congrArg ev0 hhd
    have ed : ev0 d = 1 := by
      rw [hd, eval_second_zero_sub, evalYZero_mul, restrictSecondZero_inVar_one, hw0, map_zero, mul_zero, eval_second_zero_one, sub_zero]
    have en : ev0 n = sW w := by
      rw [hn, evalYZero_add, evalYZero_mul, evalYZero_mul, eval_second_zero_at_variable_zero, restrictSecondZero_inVar_one, restrictSecondZero_inVar_one, h2,
        constantCoeff_dz_sW hw2, map_zero, map_one, mul_one, zero_mul, add_zero]
    rwa [evalYZero_mul, ed, mul_one, en] at e
  rw [hev] at hS
  rw [← hS, hhd]
end Formalism.L2.Th1.B.SAdd
