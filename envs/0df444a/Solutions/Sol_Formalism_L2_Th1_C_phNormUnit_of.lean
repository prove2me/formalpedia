-- Prove2me | solution 1 for Formalism.L2.Th1.C.phNormUnit_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:32:56.410172+00:00
-- url     : https://prove2.me/submissions/bd83dc02-5980-4f49-961a-d74aca34f8db

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_VeluIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_USideB
import Theorems.Thm_Formalism_L2_Th1_C_USideB_cc_subst
import Theorems.Thm_Formalism_L2_Th1_C_USideB_cc_mulBy
import Theorems.Thm_Formalism_L2_Th1_C_USideB_mem_intSub
import Theorems.Thm_Formalism_L2_Th1_C_USideB_C_mem_intSub
import Theorems.Thm_Formalism_L2_Th1_C_USideB_X_mem_intSub
import Theorems.Thm_Formalism_L2_Th1_C_USideB_int_of_mul
import Theorems.Thm_Formalism_L2_Th1_C_USideB_intMv_of_intPS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open USideB
namespace Formalism.L2.Th1.C
theorem _root_.solution (hE : MvExpLaws) (_hS : MvExpSubst) (hH : LGHalf) (hU : IsogenyU) :
    PhNormUnit := by
  intro K _ _ R e s2 l linv ph A c0 ι _ xP al h hph hX hI hA hxP hal hali hal0 h2 hm
  obtain ⟨L0, L1, L2, -⟩ := hE K Unit
  have mvc : ∀ f : PowerSeries K, PowerSeries.constantCoeff f = 0 →
      MvPowerSeries.constantCoeff (f : MvPowerSeries Unit K) = 0 := fun f hf => hf
  have hiso := hU K e s2 l linv ph A c0 ι xP al h hph hX hI
  have hmc : PowerSeries.constantCoeff (mulBy l linv al) = 0 := cc_mulBy h al
  have hsc : PowerSeries.constantCoeff (PowerSeries.subst (mulBy l linv al) ph) = 0 :=
    cc_subst hmc hph.1
  obtain ⟨u, hu⟩ := PowerSeries.X_dvd_iff.2 hmc
  set k := Fintype.card ι with hk
  set s := PowerSeries.subst (mulBy l linv al) ph with hs
  set D : PowerSeries K := s - ((k : K) + 1) • ph with hD
  set Q := ∏ P, (A - PowerSeries.C (xP P) * PowerSeries.X ^ 2) with hQ
  set E1 : PowerSeries K := mvExp (-((2 : K) • s)) with hE1
  set E2 : PowerSeries K := mvExp (-((2 * ((k : K) + 1)) • ph)) with hE2
  set F : PowerSeries K := mvExp ((2 * ((k : K) + 1)) • ph) with hF
  rw [hu] at hiso hm

  have h1 : u ^ 2 * E1 = PowerSeries.C (al ^ 2) * E2 * Q := by
    apply mul_left_cancel₀ (pow_ne_zero (2 * (k + 1)) (PowerSeries.X_ne_zero (R := K)))
    linear_combination hiso
  have cE1 : PowerSeries.constantCoeff E1 = 1 := L1 _ (mvc _ (by simp [hsc]))
  have cE2 : PowerSeries.constantCoeff E2 = 1 := L1 _ (mvc _ (by simp [hph.1]))
  have cQ : PowerSeries.constantCoeff Q = 1 := by simp [hQ, map_prod, hA.1]
  have cu : PowerSeries.constantCoeff u ^ 2 = al ^ 2 := by
    have h3 := congrArg PowerSeries.constantCoeff h1
    simpa [cE1, cE2, cQ] using h3
  have hu_int : IntPS R u := by
    intro n
    have h4 := hm (n + 1)
    rwa [PowerSeries.coeff_succ_X_mul] at h4
  set v := PowerSeries.C al⁻¹ * u with hv
  have hv1 : IsOneUnit R (v ^ 2) := by
    constructor
    · rw [map_pow, hv, map_mul, PowerSeries.constantCoeff_C, mul_pow, cu, inv_pow,
        inv_mul_cancel₀ (pow_ne_zero 2 hal0)]
    · exact mem_intSub.1 (pow_mem (mul_mem (C_mem_intSub hali) (mem_intSub.2 hu_int)) 2)
  have cph : PowerSeries.constantCoeff ((2 * ((k : K) + 1)) • ph) = 0 := by simp [hph.1]
  have cs2 : PowerSeries.constantCoeff (-((2 : K) • s)) = 0 := by simp [hsc]
  have hEF : E2 * F = 1 := by
    rw [hE2, hF, ← L2 _ _ (mvc _ (by simp [hph.1])) (mvc _ cph), neg_add_cancel, L0]
  have hDD : (mvExp (-(D + D)) : PowerSeries K) = E1 * F := by
    rw [hE1, hF, ← L2 _ _ (mvc _ cs2) (mvc _ cph)]
    congr 1
    rw [hD]
    module

  have hkey : (mvExp (-(D + D)) : PowerSeries K) * v ^ 2 = Q := by
    rw [hDD]
    have hv2 : v ^ 2 = PowerSeries.C al⁻¹ ^ 2 * u ^ 2 := by rw [hv, mul_pow]
    calc E1 * F * v ^ 2 = PowerSeries.C al⁻¹ ^ 2 * F * (u ^ 2 * E1) := by rw [hv2]; ring
      _ = PowerSeries.C al⁻¹ ^ 2 * F * (PowerSeries.C (al ^ 2) * E2 * Q) := by rw [h1]
      _ = PowerSeries.C (al⁻¹ ^ 2 * al ^ 2) * (E2 * F) * Q := by simp only [map_mul, map_pow]; ring
      _ = Q := by rw [hEF, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hal0), map_one]; ring
  have hAm : A ∈ intSub R := mem_intSub.2 hA.2
  have hQi : IntPS R Q := mem_intSub.1 (prod_mem fun P _ =>
    sub_mem hAm (mul_mem (C_mem_intSub (hxP P)) (pow_mem (X_mem_intSub R) 2)))
  have hI1 : IntPS R (mvExp (-(D + D)) : PowerSeries K) := int_of_mul hv1 hQi hkey
  have cD : PowerSeries.constantCoeff D = 0 := by simp [hD, hsc, hph.1]
  have cDD : PowerSeries.constantCoeff (D + D) = 0 := by simp [cD]
  have cnDD : PowerSeries.constantCoeff (-(D + D)) = 0 := by simp [cD]
  have hone : IsOneUnit R (mvExp (-(D + D)) : PowerSeries K) := ⟨L1 _ (mvc _ cnDD), hI1⟩
  have hinv : (mvExp (D + D) : PowerSeries K) * mvExp (-(D + D)) = 1 := by
    rw [← L2 _ _ (mvc _ cDD) (mvc _ cnDD), add_neg_cancel, L0]
  have hI2 : IntPS R (mvExp (D + D) : PowerSeries K) :=
    int_of_mul hone (mem_intSub.1 (one_mem _)) hinv
  exact hH K R Unit h2 D ⟨mvc _ cDD, intMv_of_intPS hI2⟩
end Formalism.L2.Th1.C
