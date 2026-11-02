-- Prove2me | solution 1 for DirectFidelity.State.eq_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T21:42:16.829556+00:00
-- url     : https://prove2.me/submissions/05c168bf-5699-49a5-b327-8e62f89a066d

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_DirectFidelity_State_Setting
import Theorems.Thm_DirectFidelity_State_prob_normalized
import Theorems.Thm_DirectFidelity_State_expectation_X
import Theorems.Thm_DirectFidelity_State_variance_X_le
set_option autoImplicit false

open DirectFidelity.State

theorem solution (n : ℕ) (ρ σ : Matrix (Q n) (Q n) ℂ) (hρ : IsPure ρ)
    (hσ : WildeQIT.IsDensityOperator σ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∑ ks ∈ Finset.univ.filter
        (fun ks : Fin (ell ε δ) → P n => ε ≤ |Y ρ σ ks - ((ρ * σ).trace).re|),
      ∏ i, prob ρ (ks i) ≤ δ := by
  set ℓ := ell ε δ
  set μ := ((ρ * σ).trace).re
  set Z : P n → ℝ := fun k => X ρ σ k - μ
  set V : ℝ := ∑ k : P n, prob ρ k * Z k ^ 2
  have h_pos_arg : 0 < 1 / (ε ^ 2 * δ) := by positivity
  have hℓ : 0 < ℓ := Nat.ceil_pos.mpr h_pos_arg
  have hℓ_ne : (ℓ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hℓ)
  have hprob : ∑ k : P n, prob ρ k = 1 := by
    have hp := DirectFidelity.State.prob_normalized n ρ hρ
    exact hp.1.trans hp.2
  have hexpX : ∑ k : P n, prob ρ k * X ρ σ k = μ :=
    DirectFidelity.State.expectation_X n ρ σ hρ hσ
  have hZ_mean : ∑ k : P n, prob ρ k * Z k = 0 := by
    have h1 : (∑ k : P n, prob ρ k * Z k) =
        (∑ k : P n, prob ρ k * X ρ σ k) - μ * (∑ k : P n, prob ρ k) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [h1, hexpX, hprob, mul_one, sub_self]
  have hV_le_one : V ≤ 1 := by
    have hV_eq : V = (∑ k : P n, prob ρ k * X ρ σ k ^ 2) - μ ^ 2 := by
      have h1 : V = (∑ k : P n, prob ρ k * X ρ σ k ^ 2) -
          2 * μ * (∑ k : P n, prob ρ k * X ρ σ k) + μ ^ 2 * (∑ k : P n, prob ρ k) := by
        simp only [V, Z]
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => by ring
      rw [h1, hexpX, hprob]
      ring
    have hvar := DirectFidelity.State.variance_X_le n ρ σ hρ hσ
    linarith [hvar.1, hvar.2]
  have h_pair : ∀ i j : Fin ℓ,
      (∑ ks : Fin ℓ → P n, (∏ r : Fin ℓ, prob ρ (ks r)) * (Z (ks i) * Z (ks j))) =
        if i = j then V else 0 := by
    intro i j
    have h1 : ∀ ks : Fin ℓ → P n,
        (∏ r : Fin ℓ, prob ρ (ks r)) * (Z (ks i) * Z (ks j)) =
          ∏ r : Fin ℓ, (prob ρ (ks r) *
            (if r = i then Z (ks r) else 1) * (if r = j then Z (ks r) else 1)) := by
      intro ks
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
      have hi : (∏ r : Fin ℓ, if r = i then Z (ks r) else 1) = Z (ks i) := by
        simp [eq_comm]
      have hj : (∏ r : Fin ℓ, if r = j then Z (ks r) else 1) = Z (ks j) := by
        simp [eq_comm]
      rw [hi, hj, mul_assoc]
    simp_rw [h1]
    rw [← Fintype.prod_sum (fun (r : Fin ℓ) (k : P n) =>
      prob ρ k * (if r = i then Z k else 1) * (if r = j then Z k else 1))]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      have h2 : ∀ r : Fin ℓ,
          (∑ k : P n, prob ρ k * (if r = i then Z k else 1) * (if r = i then Z k else 1)) =
            if r = i then V else 1 := by
        intro r
        split_ifs with hri
        · simp only [V, sq, mul_assoc]
        · simpa using hprob
      simp_rw [h2]
      simp [eq_comm]
    · rw [if_neg hij]
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      simp only [↓reduceIte, hij, mul_one]
      exact hZ_mean
  have hY_sub : ∀ ks : Fin ℓ → P n,
      (Y ρ σ ks - μ) ^ 2 = (1 / (ℓ : ℝ) ^ 2) * ∑ i : Fin ℓ, ∑ j : Fin ℓ, Z (ks i) * Z (ks j) := by
    intro ks
    have hsub : Y ρ σ ks - μ = (1 / (ℓ : ℝ)) * ∑ i : Fin ℓ, Z (ks i) := by
      simp only [Y, Z, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_sub]
      have hμ : (1 / (ℓ : ℝ)) * ((ℓ : ℝ) * μ) = μ := by
        field_simp [hℓ_ne]
      rw [hμ]
    rw [hsub, mul_pow, one_div_pow, sq (∑ i, Z (ks i)), Fintype.sum_mul_sum]
  have h_var_Y :
      (∑ ks : Fin ℓ → P n, (∏ r : Fin ℓ, prob ρ (ks r)) * (Y ρ σ ks - μ) ^ 2) =
        V / (ℓ : ℝ) := by
    simp_rw [hY_sub]
    have h_pull : ∀ ks : Fin ℓ → P n,
        (∏ r : Fin ℓ, prob ρ (ks r)) *
          ((1 / (ℓ : ℝ) ^ 2) * ∑ i : Fin ℓ, ∑ j : Fin ℓ, Z (ks i) * Z (ks j)) =
          (1 / (ℓ : ℝ) ^ 2) *
            ∑ i : Fin ℓ, ∑ j : Fin ℓ, (∏ r : Fin ℓ, prob ρ (ks r)) * (Z (ks i) * Z (ks j)) := by
      intro ks
      rw [← mul_assoc, mul_comm (∏ r, prob ρ (ks r)), mul_assoc, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
    simp_rw [h_pull]
    rw [← Finset.mul_sum, Finset.sum_comm]
    have h_inner_sum :
        (∑ i : Fin ℓ, ∑ ks : Fin ℓ → P n, ∑ j : Fin ℓ,
          (∏ r : Fin ℓ, prob ρ (ks r)) * (Z (ks i) * Z (ks j))) =
        ∑ i : Fin ℓ, ∑ j : Fin ℓ, if i = j then V else 0 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => h_pair i j
    rw [h_inner_sum]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hℓ_ne]
  have h_cheb :
      (∑ ks ∈ Finset.univ.filter (fun ks : Fin ℓ → P n => ε ≤ |Y ρ σ ks - μ|),
        ∏ i, prob ρ (ks i)) ≤
        (1 / ε ^ 2) * ∑ ks : Fin ℓ → P n, (∏ i, prob ρ (ks i)) * (Y ρ σ ks - μ) ^ 2 := by
    rw [Finset.mul_sum]
    have h_le_filter :
        (∑ ks ∈ Finset.univ.filter (fun ks : Fin ℓ → P n => ε ≤ |Y ρ σ ks - μ|),
          ∏ i, prob ρ (ks i)) ≤
        ∑ ks ∈ Finset.univ.filter (fun ks : Fin ℓ → P n => ε ≤ |Y ρ σ ks - μ|),
          (1 / ε ^ 2) * ((∏ i, prob ρ (ks i)) * (Y ρ σ ks - μ) ^ 2) := by
      refine Finset.sum_le_sum fun ks hks => ?_
      have h_abs : ε ≤ |Y ρ σ ks - μ| := (Finset.mem_filter.mp hks).2
      have h_sq : ε ^ 2 ≤ (Y ρ σ ks - μ) ^ 2 := by
        rw [← sq_abs (Y ρ σ ks - μ)]
        exact pow_le_pow_left₀ hε.le h_abs 2
      have h_one_le : 1 ≤ (1 / ε ^ 2) * (Y ρ σ ks - μ) ^ 2 := by
        rw [one_div_mul_eq_div, one_le_div (by positivity)]
        exact h_sq
      have h_prod_nonneg : 0 ≤ ∏ i : Fin ℓ, prob ρ (ks i) :=
        Finset.prod_nonneg fun i _ => sq_nonneg (chi ρ (ks i))
      calc
        (∏ i, prob ρ (ks i)) = (∏ i, prob ρ (ks i)) * 1 := (mul_one _).symm
        _ ≤ (∏ i, prob ρ (ks i)) * ((1 / ε ^ 2) * (Y ρ σ ks - μ) ^ 2) :=
            mul_le_mul_of_nonneg_left h_one_le h_prod_nonneg
        _ = (1 / ε ^ 2) * ((∏ i, prob ρ (ks i)) * (Y ρ σ ks - μ) ^ 2) := by ring
    refine h_le_filter.trans (Finset.sum_le_univ_sum_of_nonneg fun ks => ?_)
    have h_prod_nonneg : 0 ≤ ∏ i : Fin ℓ, prob ρ (ks i) :=
      Finset.prod_nonneg fun i _ => sq_nonneg (chi ρ (ks i))
    positivity
  rw [h_var_Y] at h_cheb
  have h_ceil : 1 / (ε ^ 2 * δ) ≤ (ℓ : ℝ) := Nat.le_ceil _
  have h_inv_le : 1 / (ε ^ 2 * (ℓ : ℝ)) ≤ δ := by
    have h1 : 1 ≤ (ℓ : ℝ) * (ε ^ 2 * δ) := (div_le_iff₀ (by positivity)).mp h_ceil
    rw [div_le_iff₀ (by positivity)]
    linarith
  have h_bound : (1 / ε ^ 2) * (V / (ℓ : ℝ)) ≤ 1 / (ε ^ 2 * (ℓ : ℝ)) := by
    calc
      (1 / ε ^ 2) * (V / (ℓ : ℝ)) = V / (ε ^ 2 * (ℓ : ℝ)) := by ring
      _ ≤ 1 / (ε ^ 2 * (ℓ : ℝ)) := div_le_div_of_nonneg_right hV_le_one (by positivity)
  exact h_cheb.trans (h_bound.trans h_inv_le)
