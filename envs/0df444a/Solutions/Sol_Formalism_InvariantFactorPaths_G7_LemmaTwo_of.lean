-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemmaTwo_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:11:47.888284+00:00
-- url     : https://prove2.me/submissions/85070e38-0499-4af0-be58-8efdcc173aa1

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LemmaTwoOf
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemTwo_fin_two_vector_eq_matrixVecCons
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemTwo_coeff_partial_coboundary
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemTwo_coeff_one_lgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemTwo_coeff_swap2
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemTwo_coeff_lgF_odd
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemTwo_coeff_g0F_even
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemTwo_norm_sub_le_one

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
open LemTwo
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (h1 : LemmaOne) (hL : LawSymm) : LemmaTwo := by
  intro K _ _ _ _ p σ hU F hF H hH hd hd'
  obtain ⟨hp, -, hnp, -, -⟩ := id hU
  have hp2 : 2 ≤ p := hp.two_le
  obtain ⟨hF0, -, -⟩ := id hF
  have np : ∀ k : ℕ, ‖((p : K) ^ k)⁻¹‖ = (p : ℝ) ^ k := by
    intro k
    rw [norm_inv, norm_pow, hnp, inv_pow, inv_inv]
  have zero_of_bdd : ∀ (c : K) (M : ℝ), (∀ N : ℕ, ∃ k, N ≤ k ∧ ‖c * ((p : K) ^ k)⁻¹‖ ≤ M) → c = 0 := by
    intro c M h
    by_contra hc
    have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (M / ‖c‖) hp1
    obtain ⟨k, hk, hle⟩ := h n
    rw [norm_mul, np] at hle
    have hpk : (p : ℝ) ^ n ≤ (p : ℝ) ^ k := pow_le_pow_right₀ hp1.le hk
    have h3 : M / ‖c‖ < (p : ℝ) ^ k := lt_of_lt_of_le hn hpk
    rw [div_lt_iff₀ hcpos] at h3
    linarith [mul_comm ‖c‖ ((p : ℝ) ^ k)]
  have ultra : ∀ {a b : K} {M : ℝ}, ‖a - b‖ ≤ 1 → ‖b‖ ≤ M → 1 ≤ M → ‖a‖ ≤ M := by
    intro a b M h hb hM
    calc ‖a‖ = ‖(a - b) + b‖ := by rw [sub_add_cancel]
      _ ≤ max ‖a - b‖ ‖b‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ M := max_le (h.trans hM) hb
  have hpp : 2 ≤ p ^ 2 := by nlinarith
  have lg_pow : ∀ k : ℕ, PowerSeries.coeff ((p ^ 2) ^ k) (lgF K p) = ((p : K) ^ k)⁻¹ := by
    intro k
    rw [lgF, PowerSeries.coeff_mk, Finset.sum_eq_single k]
    · rw [if_pos rfl]
    · intro j _ hj
      rw [if_neg]
      intro h
      exact hj (Nat.pow_right_injective hpp h).symm
    · intro hk
      exfalso
      apply hk
      rw [Finset.mem_range]
      have : k < (p ^ 2) ^ k := Nat.lt_pow_self (by omega)
      omega
  have g0_pow : ∀ k : ℕ, PowerSeries.coeff (p * (p ^ 2) ^ k) (g0F K p) = ((p : K) ^ (k + 1))⁻¹ := by
    intro k
    rw [g0F, PowerSeries.coeff_mk, Finset.sum_eq_single k]
    · rw [if_pos rfl]
    · intro j _ hj
      rw [if_neg]
      intro h
      exact hj (Nat.pow_right_injective hpp (Nat.eq_of_mul_eq_mul_left (by omega) h)).symm
    · intro hk
      exfalso
      apply hk
      rw [Finset.mem_range]
      have : k < (p ^ 2) ^ k := Nat.lt_pow_self (by omega)
      have : (p ^ 2) ^ k ≤ p * (p ^ 2) ^ k := Nat.le_mul_of_pos_left _ (by omega)
      omega
  have lg_zero : ∀ m : ℕ, (∀ l, m ≠ (p ^ 2) ^ l) → PowerSeries.coeff m (lgF K p) = 0 := by
    intro m hm
    rw [lgF, PowerSeries.coeff_mk]
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg (hm j)]
  have g01 : PowerSeries.coeff 1 (g0F K p) = 0 := by
    have := LemTwo.coeff_g0F_even (K := K) hp2 0
    rwa [pow_zero] at this
  have lg1 : PowerSeries.coeff 1 (lgF K p) = 1 := LemTwo.coeff_one_lgF hp2
  have hH2 : DivAB (swap2 H) := by
    intro n hn
    rw [LemTwo.fin_two_vector_eq_matrixVecCons n, LemTwo.coeff_swap2]
    apply hH
    rcases hn with h | h
    · right
      simp [h]
    · left
      simp [h]
  have cobInt : ∀ G : MvPowerSeries (Fin 2) K, Integral (d1 F G) → ∀ m, Integral (cob F (sl G m)) := by
    intro G hG m e
    rw [← LemTwo.coeff_partial_coboundary hF0 G e m]
    exact hG _
  have c0 : ∀ G : MvPowerSeries (Fin 2) K, DivAB G → ∀ m, PowerSeries.constantCoeff (sl G m) = 0 := by
    intro G hG m
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, sl, PowerSeries.coeff_mk]
    apply hG
    left
    simp
  choose α β R hα hR hsl using fun m => h1 K p σ hU F hF (sl H m) (c0 H hH m) (cobInt H hd m)
  choose α' β' R' hα' hR' hsl' using fun m =>
    h1 K p σ hU F hF (sl (swap2 H) m) (c0 _ hH2 m) (cobInt _ hd' m)
  have cH : ∀ i m, MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 m) H =
      α m * PowerSeries.coeff i (g0F K p) + β m * PowerSeries.coeff i (lgF K p) +
        PowerSeries.coeff i (R m) := by
    intro i m
    have h3 := congrArg (PowerSeries.coeff i) (hsl m)
    rw [sl, PowerSeries.coeff_mk] at h3
    rw [h3, map_add, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
  have cH' : ∀ i m, MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 m) H =
      α' i * PowerSeries.coeff m (g0F K p) + β' i * PowerSeries.coeff m (lgF K p) +
        PowerSeries.coeff m (R' i) := by
    intro i m
    have h3 := congrArg (PowerSeries.coeff m) (hsl' i)
    rw [sl, PowerSeries.coeff_mk, LemTwo.coeff_swap2] at h3
    rw [h3, map_add, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
  have star : ∀ i m, ‖(α m * PowerSeries.coeff i (g0F K p) + β m * PowerSeries.coeff i (lgF K p)) -
      (α' i * PowerSeries.coeff m (g0F K p) + β' i * PowerSeries.coeff m (lgF K p))‖ ≤ 1 := by
    intro i m
    have e : (α m * PowerSeries.coeff i (g0F K p) + β m * PowerSeries.coeff i (lgF K p)) -
        (α' i * PowerSeries.coeff m (g0F K p) + β' i * PowerSeries.coeff m (lgF K p)) =
        PowerSeries.coeff m (R' i) - PowerSeries.coeff i (R m) := by
      have e1 := cH i m
      have e2 := cH' i m
      linear_combination e2 - e1
    rw [e]
    exact LemTwo.norm_sub_le_one (hR' i m) (hR m i)
  have hA : ∀ k, β' (p * (p ^ 2) ^ k) = 0 := by
    intro k
    apply zero_of_bdd _ ((p : ℝ) ^ (k + 1))
    intro N
    refine ⟨N, le_rfl, ?_⟩
    have s := star (p * (p ^ 2) ^ k) ((p ^ 2) ^ N)
    rw [g0_pow k, LemTwo.coeff_lgF_odd hp2 k, LemTwo.coeff_g0F_even hp2 N, lg_pow N] at s
    simp only [mul_zero, add_zero, zero_add] at s
    refine ultra (b := α ((p ^ 2) ^ N) * ((p : K) ^ (k + 1))⁻¹) ?_ ?_
      (one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ p)))
    · rw [norm_sub_rev]
      exact s
    · rw [norm_mul, np]
      exact mul_le_of_le_one_left (by positivity) (hα _)
  have hB : ∀ m, α m = 0 := by
    intro m
    apply zero_of_bdd _ (max 1 ‖PowerSeries.coeff m (g0F K p)‖)
    intro N
    refine ⟨N + 1, by omega, ?_⟩
    have s := star (p * (p ^ 2) ^ N) m
    rw [g0_pow N, LemTwo.coeff_lgF_odd hp2 N, hA N] at s
    simp only [mul_zero, add_zero, zero_mul] at s
    refine ultra (b := α' (p * (p ^ 2) ^ N) * PowerSeries.coeff m (g0F K p)) s ?_ (le_max_left _ _)
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hα' _)).trans (le_max_right _ _)
  have hC : ∀ m, (∀ l, m ≠ (p ^ 2) ^ l) → β m = 0 := by
    intro m hm
    apply zero_of_bdd _ (max 1 ‖PowerSeries.coeff m (g0F K p)‖)
    intro N
    refine ⟨N, le_rfl, ?_⟩
    have s := star ((p ^ 2) ^ N) m
    rw [LemTwo.coeff_g0F_even hp2 N, lg_pow N, lg_zero m hm, hB m] at s
    simp only [mul_zero, zero_mul, add_zero, zero_add] at s
    refine ultra (b := α' ((p ^ 2) ^ N) * PowerSeries.coeff m (g0F K p)) s ?_ (le_max_left _ _)
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hα' _)).trans (le_max_right _ _)
  have hD : ∀ l, β ((p ^ 2) ^ l) = β 1 * ((p : K) ^ l)⁻¹ := by
    intro l
    rw [← sub_eq_zero]
    apply zero_of_bdd _ ((p : ℝ) ^ l)
    intro N
    refine ⟨N, le_rfl, ?_⟩
    have s1 := star ((p ^ 2) ^ N) ((p ^ 2) ^ l)
    have s2 := star ((p ^ 2) ^ N) 1
    rw [LemTwo.coeff_g0F_even hp2 N, lg_pow N, LemTwo.coeff_g0F_even hp2 l, lg_pow l, hB] at s1
    rw [LemTwo.coeff_g0F_even hp2 N, lg_pow N, g01, lg1, hB] at s2
    simp only [mul_zero, zero_mul, add_zero, zero_add, mul_one] at s1 s2
    have e : (β ((p ^ 2) ^ l) - β 1 * ((p : K) ^ l)⁻¹) * ((p : K) ^ N)⁻¹ =
        (β ((p ^ 2) ^ l) * ((p : K) ^ N)⁻¹ - β' ((p ^ 2) ^ N) * ((p : K) ^ l)⁻¹) -
          ((p : K) ^ l)⁻¹ * (β 1 * ((p : K) ^ N)⁻¹ - β' ((p ^ 2) ^ N)) := by ring
    rw [e]
    have usub : ∀ a b : K, ‖a - b‖ ≤ max ‖a‖ ‖b‖ := fun a b => by
      rw [sub_eq_add_neg]
      have h4 := IsUltrametricDist.norm_add_le_max a (-b)
      rwa [norm_neg] at h4
    refine (usub _ _).trans (max_le ?_ ?_)
    · exact s1.trans (one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ p)))
    · rw [norm_mul, np]
      exact mul_le_of_le_one_right (by positivity) s2
  refine ⟨β 1, H - MvPowerSeries.C (β 1) * (at1 0 (lgF K p) * at1 1 (lgF K p)), ?_, by ring⟩
  intro n
  rw [LemTwo.fin_two_vector_eq_matrixVecCons n]
  set i := n 0
  set m := n 1
  rw [map_sub, MvPowerSeries.coeff_C_mul, at1, at1, PowerSeries.coeff_subst_X_zero_subst_mul_X_one, cH,
    hB m]
  have ev0 : (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) m : Fin 2 →₀ ℕ) 0 = i := by simp
  have ev1 : (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) m : Fin 2 →₀ ℕ) 1 = m := by simp
  rw [ev0, ev1]
  have key : β m * PowerSeries.coeff i (lgF K p) -
      β 1 * (PowerSeries.coeff i (lgF K p) * PowerSeries.coeff m (lgF K p)) = 0 := by
    by_cases hm : ∃ l, m = (p ^ 2) ^ l
    · obtain ⟨l, hl⟩ := hm
      rw [hl, hD l, lg_pow l]
      ring
    · push_neg at hm
      rw [hC m hm, lg_zero m hm]
      ring
  have e : 0 * PowerSeries.coeff i (g0F K p) + β m * PowerSeries.coeff i (lgF K p) + PowerSeries.coeff i (R m) -
      β 1 * (PowerSeries.coeff i (lgF K p) * PowerSeries.coeff m (lgF K p)) =
      PowerSeries.coeff i (R m) + (β m * PowerSeries.coeff i (lgF K p) -
        β 1 * (PowerSeries.coeff i (lgF K p) * PowerSeries.coeff m (lgF K p))) := by ring
  rw [e, key, add_zero]
  exact hR m i
end Formalism.InvariantFactorPaths.G7
