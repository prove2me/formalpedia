-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.derivative_a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:44:10.443641+00:00
-- url     : https://prove2.me/submissions/e8a89fbb-b125-4802-a747-a2f88158ab1d

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LocalComponentGL
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_IntegralPderivLgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DividedPowerNorms_norm_p_pos
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DividedPowerNorms_norm_p_pow_le_one
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_Aser_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_PhiH_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_natCast
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_frob_congr
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_sm_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_AA_ne_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_AA_of
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_g0F_ne_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_g0F_of
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_lgF_ne_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_lgF_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_product_single_variables
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_powq_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ppowq_inj
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_Aser__eq_f9daf344d726


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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open DworkIntegrality (Bd bd_add bd_sub bd_mul bd_C bd_sum int_mul int_pow sm_mul bd_natCast frob_congr
  PhiH PhiH_apply)
open DividedPowerNorms
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution : DerivA := by
  intro K _ _ _ p hp hnp
  have hp2 := hp.two_le
  have hpK : (p : K) ≠ 0 := norm_pos_iff.mp (norm_p_pos hp hnp)
  have a0 : ∀ n : Fin 2 →₀ ℕ, (n + Finsupp.single 0 1 : Fin 2 →₀ ℕ) 0 = n 0 + 1 := fun n => by simp
  have a1 : ∀ n : Fin 2 →₀ ℕ, (n + Finsupp.single 0 1 : Fin 2 →₀ ℕ) 1 = n 1 := fun n => by simp
  have hcast : ∀ n : Fin 2 →₀ ℕ, (n 0 : K) + 1 = ((n 0 + 1 : ℕ) : K) := fun n => by push_cast; rfl
  constructor
  · intro n
    rw [map_sub, MvPowerSeries.coeff_pderiv, coeff_product_single_variables (by decide) (by decide),
      PowerSeries.coeff_derivative, Aser_eq, hcast]
    by_cases h : ∃ i j, n 0 + 1 = (p ^ 2) ^ i ∧ n 1 = p * (p ^ 2) ^ j
    · obtain ⟨i, j, hi, hj⟩ := h
      rw [hi, hj, coeff_lgF_pow K hp2, coeff_g0F_of K hp2]
      by_cases hij : i ≤ j
      · rw [coeff_AA_of K hp2 hij ((a0 n).trans hi) ((a1 n).trans hj)]
        have : ((p : K) ^ (i + j + 1))⁻¹ * (((p ^ 2) ^ i : ℕ) : K) -
            ((p : K) ^ i)⁻¹ * (((p ^ 2) ^ i : ℕ) : K) * ((p : K) ^ (j + 1))⁻¹ = 0 := by
          rw [add_assoc, pow_add, mul_inv]
          ring
        rw [this]
        simp
      · have hz : MvPowerSeries.coeff (n + Finsupp.single 0 1) (AA K p 0 1) = 0 := by
          by_contra hne
          obtain ⟨i', j', hij', hi', hj'⟩ := coeff_AA_ne_zero hne
          rw [a0, hi] at hi'
          rw [a1, hj] at hj'
          rw [powq_inj hp2 hi', ppowq_inj hp2 hj'] at hij
          exact hij hij'
        obtain ⟨e, rfl⟩ : ∃ e, i = j + 1 + e := ⟨i - (j + 1), by omega⟩
        have : ((p : K) ^ (j + 1 + e))⁻¹ * (((p ^ 2) ^ (j + 1 + e) : ℕ) : K) *
            ((p : K) ^ (j + 1))⁻¹ = (p : K) ^ e := by
          push_cast
          field_simp
          ring
        rw [hz, zero_mul, zero_sub, norm_neg, this]
        exact norm_p_pow_le_one hp hnp e
    · have hz : MvPowerSeries.coeff (n + Finsupp.single 0 1) (AA K p 0 1) = 0 := by
        by_contra hne
        obtain ⟨i', j', _, hi', hj'⟩ := coeff_AA_ne_zero hne
        exact h ⟨i', j', (a0 n).symm.trans hi', (a1 n).symm.trans hj'⟩
      have hz2 : PowerSeries.coeff (n 0 + 1) (lgF K p) * PowerSeries.coeff (n 1) (g0F K p) = 0 := by
        by_contra hne
        obtain ⟨i', hi'⟩ := coeff_lgF_ne_zero (left_ne_zero_of_mul hne)
        obtain ⟨j', hj'⟩ := coeff_g0F_ne_zero (right_ne_zero_of_mul hne)
        exact h ⟨i', j', hi', hj'⟩
      rw [hz, zero_mul, zero_sub, norm_neg, mul_right_comm, hz2, zero_mul]
      simp
  · intro n
    rw [MvPowerSeries.coeff_pderiv, Aser'_eq, hcast]
    by_cases hne : MvPowerSeries.coeff (n + Finsupp.single 0 1) (AA K p 1 0) = 0
    · rw [hne, zero_mul]
      simp
    obtain ⟨i, j, hij, hi, hj⟩ := coeff_AA_ne_zero hne
    rw [coeff_AA_of K hp2 hij hi hj]
    rw [a0] at hj
    rw [hj]
    obtain ⟨e, rfl⟩ : ∃ e, j = i + e := ⟨j - i, by omega⟩
    have : ((p : K) ^ (i + (i + e) + 1))⁻¹ * ((p * (p ^ 2) ^ (i + e) : ℕ) : K) = (p : K) ^ e := by
      push_cast
      field_simp
      ring
    rw [this]
    exact norm_p_pow_le_one hp hnp e
end Formalism.InvariantFactorPaths.G7
