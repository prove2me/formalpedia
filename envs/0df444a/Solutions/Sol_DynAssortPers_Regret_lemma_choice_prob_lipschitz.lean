-- Prove2me | solution 1 for DynAssortPers.Regret.lemma_choice_prob_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T12:52:06.57961+00:00
-- url     : https://prove2.me/submissions/fb9a1095-810d-45f0-9f24-b1bebdcbe544

import Mathlib
import Definitions.Def_DynAssortPers_Regret_MNL

open DynAssortPers.Regret

namespace DAPcpl

/-- derivative of the choice probability along the line `θ + s d`. -/
lemma hasDeriv_line {n : ℕ} (S : Finset (Fin n)) (j : Fin n) (hj : j ∈ S)
    (θ d : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => choiceProb (fun k => θ k + s * d k) S j)
      (∑ k ∈ S, ((if k = j then Real.exp (θ j + s * d j) / (1 + ∑ k' ∈ S, Real.exp (θ k' + s * d k')) else 0)
        - Real.exp (θ j + s * d j) / (1 + ∑ k' ∈ S, Real.exp (θ k' + s * d k')) *
          (Real.exp (θ k + s * d k) / (1 + ∑ k' ∈ S, Real.exp (θ k' + s * d k')))) * d k) s := by
  have hE : ∀ k, HasDerivAt (fun s : ℝ => Real.exp (θ k + s * d k))
      (Real.exp (θ k + s * d k) * d k) s := by
    intro k
    have h1 : HasDerivAt (fun s : ℝ => θ k + s * d k) (d k) s := by
      simpa using ((hasDerivAt_id s).mul_const (d k)).const_add (θ k)
    exact h1.exp
  have hD : HasDerivAt (fun s : ℝ => 1 + ∑ k ∈ S, Real.exp (θ k + s * d k))
      (∑ k ∈ S, Real.exp (θ k + s * d k) * d k) s := by
    have := HasDerivAt.fun_sum (u := S) (fun k _ => hE k)
    simpa using this.const_add 1
  have hDpos : ∀ s : ℝ, 0 < 1 + ∑ k ∈ S, Real.exp (θ k + s * d k) := fun s => by
    have := Finset.sum_nonneg (s := S) (fun k _ => (Real.exp_pos (θ k + s * d k)).le)
    linarith
  have hf : (fun s : ℝ => choiceProb (fun k => θ k + s * d k) S j) =
      fun s => Real.exp (θ j + s * d j) / (1 + ∑ k ∈ S, Real.exp (θ k + s * d k)) := by
    funext s; simp [choiceProb, hj]
  rw [hf]
  refine ((hE j).div hD (hDpos s).ne').congr_deriv ?_
  symm
  set D := 1 + ∑ k' ∈ S, Real.exp (θ k' + s * d k') with hDdef
  have hD0 : D ≠ 0 := (hDpos s).ne'
  have e1 : ∀ k ∈ S, ((if k = j then Real.exp (θ j + s * d j) / D else 0)
        - Real.exp (θ j + s * d j) / D * (Real.exp (θ k + s * d k) / D)) * d k
      = (if k = j then Real.exp (θ j + s * d j) / D * d k else 0)
        - Real.exp (θ j + s * d j) / D ^ 2 * (Real.exp (θ k + s * d k) * d k) := by
    intro k _
    split_ifs <;> field_simp <;> ring
  rw [Finset.sum_congr rfl e1, Finset.sum_sub_distrib, Finset.sum_ite_eq' S j, if_pos hj,
    ← Finset.mul_sum]
  field_simp

/-- pointwise coefficient bounds. -/
lemma coef_sq_le {n : ℕ} (S : Finset (Fin n)) (j : Fin n) (hj : j ∈ S) (e : Fin n → ℝ)
    (he : ∀ k, 0 < e k) (k : Fin n) (hk : k ∈ S) :
    ((if k = j then e j / (1 + ∑ k' ∈ S, e k') else 0)
        - e j / (1 + ∑ k' ∈ S, e k') * (e k / (1 + ∑ k' ∈ S, e k'))) ^ 2 ≤ 1 / 16 ∧
      (k ≠ j → ((if k = j then e j / (1 + ∑ k' ∈ S, e k') else 0)
        - e j / (1 + ∑ k' ∈ S, e k') * (e k / (1 + ∑ k' ∈ S, e k'))) ^ 2 < 1 / 16) := by
  set D := 1 + ∑ k' ∈ S, e k' with hD
  have hsum : ∀ k ∈ S, e k ≤ ∑ k' ∈ S, e k' := fun k hk =>
    Finset.single_le_sum (fun i _ => (he i).le) hk
  have hDpos : 0 < D := by have := hsum j hj; have := he j; linarith
  have hpj : 0 < e j / D := div_pos (he j) hDpos
  have hpj1 : e j / D < 1 := by rw [div_lt_one hDpos]; have := hsum j hj; linarith
  refine ⟨?_, ?_⟩
  · by_cases hkj : k = j
    · subst hkj
      simp only [if_true]
      set p := e k / D
      have hx1 : p - p * p ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1/2)]
      have hx0 : 0 ≤ p - p * p := by nlinarith
      nlinarith
    · simp only [hkj, if_false]
      have hpk : 0 < e k / D := div_pos (he k) hDpos
      have hpair : e j + e k ≤ ∑ k' ∈ S, e k' := by
        have := Finset.sum_le_sum_of_subset_of_nonneg (f := e) (s := {j, k}) (t := S)
          (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption)
          (fun i _ _ => (he i).le)
        rwa [Finset.sum_pair (Ne.symm hkj)] at this
      have hlt : e j / D + e k / D < 1 := by
        rw [← add_div, div_lt_one hDpos]; linarith
      set p := e j / D
      set q := e k / D
      have : p * q < 1 / 4 := by nlinarith [sq_nonneg (p - q)]
      nlinarith [mul_pos hpj hpk]
  · intro hkj
    simp only [hkj, if_false]
    have hpk : 0 < e k / D := div_pos (he k) hDpos
    have hpair : e j + e k ≤ ∑ k' ∈ S, e k' := by
      have := Finset.sum_le_sum_of_subset_of_nonneg (f := e) (s := {j, k}) (t := S)
        (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption)
        (fun i _ _ => (he i).le)
      rwa [Finset.sum_pair (Ne.symm hkj)] at this
    have hlt : e j / D + e k / D < 1 := by
      rw [← add_div, div_lt_one hDpos]; linarith
    set p := e j / D
    set q := e k / D
    have : p * q < 1 / 4 := by nlinarith [sq_nonneg (p - q)]
    nlinarith [mul_pos hpj hpk]

/-- the coefficient `a_k(s)` of the derivative. -/
noncomputable def coef {n : ℕ} (S : Finset (Fin n)) (j : Fin n) (θ d : Fin n → ℝ) (s : ℝ)
    (k : Fin n) : ℝ :=
  (if k = j then Real.exp (θ j + s * d j) / (1 + ∑ k' ∈ S, Real.exp (θ k' + s * d k')) else 0)
    - Real.exp (θ j + s * d j) / (1 + ∑ k' ∈ S, Real.exp (θ k' + s * d k')) *
      (Real.exp (θ k + s * d k) / (1 + ∑ k' ∈ S, Real.exp (θ k' + s * d k')))

lemma hasDeriv_line' {n : ℕ} (S : Finset (Fin n)) (j : Fin n) (hj : j ∈ S)
    (θ d : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => choiceProb (fun k => θ k + s * d k) S j)
      (∑ k ∈ S, coef S j θ d s k * d k) s := hasDeriv_line S j hj θ d s

lemma coef_sum_sq_le {n : ℕ} (S : Finset (Fin n)) (j : Fin n) (hj : j ∈ S)
    (θ d : Fin n → ℝ) (s : ℝ) :
    ∑ k ∈ S, coef S j θ d s k ^ 2 ≤ (S.card : ℝ) / 16 := by
  have := Finset.sum_le_sum (s := S) (fun k hk =>
    (coef_sq_le S j hj (fun k => Real.exp (θ k + s * d k)) (fun k => Real.exp_pos _) k hk).1)
  simpa [coef, div_eq_mul_inv, mul_comm] using this

lemma coef_sum_sq_lt {n : ℕ} (S : Finset (Fin n)) (j : Fin n) (hj : j ∈ S) (hS : 2 ≤ S.card)
    (θ d : Fin n → ℝ) (s : ℝ) :
    ∑ k ∈ S, coef S j θ d s k ^ 2 < (S.card : ℝ) / 16 := by
  obtain ⟨k, hk, hkj⟩ := Finset.exists_mem_ne (s := S) (by omega) j
  have := Finset.sum_lt_sum (s := S) (f := fun k => coef S j θ d s k ^ 2) (g := fun _ => (1:ℝ)/16)
    (fun k hk =>
    (coef_sq_le S j hj (fun k => Real.exp (θ k + s * d k)) (fun k => Real.exp_pos _) k hk).1)
    ⟨k, hk, (coef_sq_le S j hj (fun k => Real.exp (θ k + s * d k)) (fun k => Real.exp_pos _) k
      hk).2 hkj⟩
  simpa [div_eq_mul_inv, mul_comm] using this

lemma deriv_sq_le {n : ℕ} (S : Finset (Fin n)) (j : Fin n) (hj : j ∈ S)
    (θ d : Fin n → ℝ) (s : ℝ) :
    (∑ k ∈ S, coef S j θ d s k * d k) ^ 2 ≤
      (∑ k ∈ S, coef S j θ d s k ^ 2) * ∑ k : Fin n, d k ^ 2 := by
  refine (Finset.sum_mul_sq_le_sq_mul_sq S _ _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    (fun _ _ _ => sq_nonneg _)

lemma mvt {n : ℕ} (S : Finset (Fin n)) (j : Fin n) (hj : j ∈ S) (θ θ' : Fin n → ℝ) :
    ∃ c ∈ Set.Ioo (0:ℝ) 1, choiceProb θ' S j - choiceProb θ S j =
      ∑ k ∈ S, coef S j θ (fun k => θ' k - θ k) c k * (θ' k - θ k) := by
  obtain ⟨c, hc, h⟩ := exists_hasDerivAt_eq_slope
    (fun s : ℝ => choiceProb (fun k => θ k + s * (θ' k - θ k)) S j)
    (fun s => ∑ k ∈ S, coef S j θ (fun k => θ' k - θ k) s k * (θ' k - θ k)) zero_lt_one
    (fun x _ => (hasDeriv_line' S j hj θ _ x).continuousAt.continuousWithinAt)
    (fun x _ => hasDeriv_line' S j hj θ _ x)
  refine ⟨c, hc, ?_⟩
  rw [h]; simp

lemma bound_sq {n : ℕ} (S : Finset (Fin n)) (θ θ' : Fin n → ℝ) :
    ((1 / 4) * Real.sqrt (S.card : ℝ) * euclidDist θ θ') ^ 2 =
      (S.card : ℝ) / 16 * ∑ k : Fin n, (θ' k - θ k) ^ 2 := by
  have e : ∑ k : Fin n, (θ' k - θ k) ^ 2 = ∑ k : Fin n, (θ k - θ' k) ^ 2 := by
    congr 1; funext k; ring
  rw [e, euclidDist, mul_pow, mul_pow, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  ring

theorem lip {n : ℕ} (S : Finset (Fin n)) (j : Fin n) (hj : j ∈ S)
    (θ θ' : Fin n → ℝ) :
    |choiceProb θ S j - choiceProb θ' S j| ≤
      (1 / 4) * Real.sqrt (S.card : ℝ) * euclidDist θ θ' := by
  obtain ⟨c, _, h⟩ := mvt S j hj θ θ'
  rw [abs_sub_comm, h]
  refine abs_le_of_sq_le_sq ?_ (by unfold euclidDist; positivity)
  rw [bound_sq]
  refine (deriv_sq_le S j hj θ _ c).trans ?_
  exact mul_le_mul_of_nonneg_right (coef_sum_sq_le S j hj θ _ c)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem lip_strict_two {n : ℕ} (S : Finset (Fin n)) (j : Fin n) (hj : j ∈ S) (hS : 2 ≤ S.card)
    (θ θ' : Fin n → ℝ) (hd : 0 < euclidDist θ θ') :
    |choiceProb θ S j - choiceProb θ' S j| <
      (1 / 4) * Real.sqrt (S.card : ℝ) * euclidDist θ θ' := by
  obtain ⟨c, _, h⟩ := mvt S j hj θ θ'
  rw [abs_sub_comm, h]
  refine abs_lt_of_sq_lt_sq ?_ (by positivity)
  rw [bound_sq]
  have hpos : 0 < ∑ k : Fin n, (θ' k - θ k) ^ 2 := by
    have h2 := bound_sq S θ θ'
    have : 0 < ((1 / 4) * Real.sqrt (S.card : ℝ) * euclidDist θ θ') ^ 2 := by
      have : 0 < Real.sqrt (S.card : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < S.card))
      positivity
    rw [h2] at this
    exact pos_of_mul_pos_right this (by positivity)
  refine (deriv_sq_le S j hj θ _ c).trans_lt ?_
  exact mul_lt_mul_of_pos_right (coef_sum_sq_lt S j hj hS θ _ c) hpos

end DAPcpl

theorem solution {n : ℕ} (S : Finset (Fin n)) (j : Fin n) (hj : j ∈ S)
    (θ θ' : Fin n → ℝ) :
    |choiceProb θ S j - choiceProb θ' S j| ≤
      (1 / 4) * Real.sqrt (S.card : ℝ) * euclidDist θ θ' :=
  DAPcpl.lip S j hj θ θ'
