-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.StepZero_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:00:49.836375+00:00
-- url     : https://prove2.me/submissions/569454b9-b0b2-4c05-ac04-b40e69b0c688

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ScalingSwapLemmas
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_swap_two_C_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_swap_two_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_constant_coeff_scale_two
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_constant_coeff_scale_three
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_subst_scale_three_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_coeff_subst_scale_two
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_subst_scale_two_comp
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_subst_scale_two_one
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_swap_two_subst_scale_two
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_partial_coboundary_subst_scale
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_partial_coboundary_C_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_partial_coboundary_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_simeq_iff_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_simeq_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_integral_scale_two
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_integral_scale_three
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_norm_of_pow_eq_one

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
open TwoVariableSwapLemmas
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (hM : LamModule) (hS : SimeqRules) (hL : LawSymm) : StepZero := by
  intro K _ _ _ p σ hU hζ F hF be hbe
  obtain ⟨hp, hp2, hpn, -, hσ⟩ := hU
  obtain ⟨ζ, hζ⟩ := hζ
  obtain ⟨hdiv, hd1, hd2, hrot⟩ := hbe
  have hF0 : MvPowerSeries.constantCoeff F = 0 := hF.1
  have hsym := (hL K p hp hpn F hF).2.1
  obtain ⟨N, hN⟩ : ∃ N, N = p ^ 2 - 1 := ⟨_, rfl⟩
  rw [← hN] at hζ hrot hsym
  have hsq : p ^ 2 = N + 1 := by
    have : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
    omega
  have hN0 : N ≠ 0 := by
    intro h0
    rw [h0] at hsq
    nlinarith
  have hNp : ¬ p ∣ N := by
    intro hd
    have h1 : p ∣ N + 1 := by rw [← hsq]; exact dvd_pow_self p two_ne_zero
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right hd).1 h1))
  have hNK : (N : K) ≠ 0 := Nat.cast_ne_zero.2 hN0
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN0

  have hη : ∀ k : ℕ, (ζ ^ k) ^ N = 1 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hθ : ∀ k : ℕ, (ζ⁻¹ ^ (p * k)) ^ N = 1 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul, inv_pow, hζ.pow_eq_one, inv_one, one_pow]
  have hηθ : ∀ k : ℕ, (ζ ^ k) ^ p * ζ⁻¹ ^ (p * k) = 1 := fun k => by
    rw [← pow_mul, mul_comm k p, ← mul_pow, mul_inv_cancel₀ hζ0, one_pow]
  have hηn : ∀ k : ℕ, ‖ζ ^ k‖ ≤ 1 := fun k => (norm_of_pow_eq_one hN0 (hη k)).le
  have hθn : ∀ k : ℕ, ‖ζ⁻¹ ^ (p * k)‖ ≤ 1 := fun k => (norm_of_pow_eq_one hN0 (hθ k)).le

  have havg : ∀ (ι : Type) [Finite ι] (f : ℕ → MvPowerSeries ι K), (∀ k, Simeq (f k) 0) →
      Simeq (MvPowerSeries.C ((N : K)⁻¹) * ∑ k ∈ range N, f k) 0 := fun ι _ f hf =>
    hM K ι p σ hp hpn hσ _ N hNp (simeq_sum hS _ f fun k _ => hf k)

  have hB : ∀ k : ℕ, Simeq (MvPowerSeries.subst (sc2 (ζ ^ k) (ζ⁻¹ ^ (p * k))) be) be := by
    intro k
    have h1 := (hS K (Fin 2)).2.2.2.2 (Fin 2) _ _ (sc2 1 (ζ⁻¹ ^ (p * k))) (constant_coeff_scale_two _ _)
      (integral_scale_two (by simp) (hθn k)) (hrot (ζ ^ k) (hη k))
    have e1 : (![MvPowerSeries.C (ζ ^ k) * (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
        MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) K) = sc2 (ζ ^ k) 1 := by
      simp [sc2]
    have e2 : (![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
        MvPowerSeries.C ((ζ ^ k) ^ p) * MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) K) =
        sc2 1 ((ζ ^ k) ^ p) := by
      simp [sc2]
    rw [e1, e2, subst_scale_two_comp, subst_scale_two_comp, hηθ k, mul_one, one_mul, one_mul, subst_scale_two_one]
      at h1
    exact h1
  refine ⟨MvPowerSeries.C ((N : K)⁻¹) *
    ∑ k ∈ range N, MvPowerSeries.subst (sc2 (ζ ^ k) (ζ⁻¹ ^ (p * k))) be, ?_, ?_, ?_, ?_⟩
  ·
    intro n hn
    have hc : MvPowerSeries.coeff n (MvPowerSeries.C ((N : K)⁻¹) *
        ∑ k ∈ range N, MvPowerSeries.subst (sc2 (ζ ^ k) (ζ⁻¹ ^ (p * k))) be) =
        (N : K)⁻¹ * ((∑ k ∈ range N, (ζ ^ n 0 * ζ⁻¹ ^ (p * n 1)) ^ k) *
          MvPowerSeries.coeff n be) := by
      rw [MvPowerSeries.coeff_C_mul, map_sum, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [coeff_subst_scale_two, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm k (n 0),
        mul_assoc p k, mul_assoc p (n 1), mul_comm k (n 1)]
    rw [hc] at hn
    have hbe : MvPowerSeries.coeff n be ≠ 0 := fun h => hn (by rw [h, mul_zero, mul_zero])
    have hsum : ∑ k ∈ range N, (ζ ^ n 0 * ζ⁻¹ ^ (p * n 1)) ^ k ≠ 0 :=
      fun h => hn (by rw [h, zero_mul, mul_zero])
    have hω : ζ ^ n 0 * ζ⁻¹ ^ (p * n 1) = 1 := by
      by_contra hne
      apply hsum
      rw [geom_sum_eq hne, mul_pow, ← pow_mul, ← pow_mul, mul_comm (n 0), mul_comm (p * n 1),
        pow_mul, pow_mul ζ⁻¹, inv_pow, hζ.pow_eq_one]
      simp
    rw [inv_pow, mul_inv_eq_one₀ (pow_ne_zero _ hζ0)] at hω
    refine ⟨?_, ?_, ?_⟩
    · by_contra h
      exact hbe (hdiv n (Or.inl (by omega)))
    · by_contra h
      exact hbe (hdiv n (Or.inr (by omega)))
    · rw [← hN, Nat.modEq_iff_dvd, ← hζ.zpow_eq_one_iff_dvd, zpow_sub₀ hζ0, zpow_natCast,
        zpow_natCast, hω, div_self (pow_ne_zero _ hζ0)]
  ·
    rw [simeq_iff_sub]
    have he : MvPowerSeries.C ((N : K)⁻¹) *
        ∑ k ∈ range N, MvPowerSeries.subst (sc2 (ζ ^ k) (ζ⁻¹ ^ (p * k))) be - be =
        MvPowerSeries.C ((N : K)⁻¹) *
          ∑ k ∈ range N, (MvPowerSeries.subst (sc2 (ζ ^ k) (ζ⁻¹ ^ (p * k))) be - be) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, card_range, mul_sub, nsmul_eq_mul, ← mul_assoc,
        ← map_natCast (MvPowerSeries.C (σ := Fin 2) (R := K)) N, ← map_mul, inv_mul_cancel₀ hNK,
        map_one, one_mul]
    rw [he]
    exact havg (Fin 2) _ fun k => (simeq_iff_sub _ _).1 (hB k)
  ·
    rw [partial_coboundary_C_mul hF0, partial_coboundary_sum hF0]
    apply havg (Fin 3)
    intro k
    rw [partial_coboundary_subst_scale hF0 _ (hsym _ (hη k))]
    have h1 := (hS K (Fin 3)).2.2.2.2 (Fin 3) _ _ (sc3 (ζ ^ k) (ζ⁻¹ ^ (p * k))) (constant_coeff_scale_three _ _)
      (integral_scale_three (hηn k) (hθn k)) hd1
    rwa [subst_scale_three_zero] at h1
  ·
    rw [swap_two_C_mul, swap_two_sum, partial_coboundary_C_mul hF0, partial_coboundary_sum hF0]
    apply havg (Fin 3)
    intro k
    rw [swap_two_subst_scale_two, partial_coboundary_subst_scale hF0 _ (hsym _ (hθ k))]
    have h1 := (hS K (Fin 3)).2.2.2.2 (Fin 3) _ _ (sc3 (ζ⁻¹ ^ (p * k)) (ζ ^ k)) (constant_coeff_scale_three _ _)
      (integral_scale_three (hθn k) (hηn k)) hd2
    rwa [subst_scale_three_zero] at h1
end Formalism.InvariantFactorPaths.G7
