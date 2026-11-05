-- Prove2me | solution 1 for DynAssortPers.Regret.lemma_optimal_set_stable
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T12:56:33.401025+00:00
-- url     : https://prove2.me/submissions/e12425aa-e332-4ef2-a83e-a2dc586477d7

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


lemma revenue_eq {n : ℕ} (S : Finset (Fin n)) (w θ : Fin n → ℝ) :
    revenue S w θ = ∑ j ∈ S, w j * choiceProb θ S j := by
  unfold revenue ChoiceCDLP.MNL.mnlObjective
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  simp only [choiceProb, if_pos hj]
  rw [add_comm (∑ j ∈ S, Real.exp (θ j)) 1]
  ring

lemma le_supNorm {n : ℕ} (w : Fin n → ℝ) (j : Fin n) : |w j| ≤ supNorm w :=
  le_ciSup (f := fun j => |w j|) (Finite.bddAbove_range _) j

lemma supNorm_nonneg {n : ℕ} (w : Fin n → ℝ) : 0 ≤ supNorm w :=
  Real.iSup_nonneg (fun j => abs_nonneg (w j))

lemma rpow_three_halves (x : ℝ) (hx : 0 ≤ x) : x ^ ((3 : ℝ) / 2) = x * Real.sqrt x := by
  rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num,
    Real.rpow_add' hx (by norm_num), Real.rpow_one]

lemma card_mul_sqrt_le {n : ℕ} (S : Finset (Fin n)) (K : ℕ) (hS : S.card ≤ K) :
    (S.card : ℝ) * Real.sqrt (S.card : ℝ) ≤ (K : ℝ) ^ ((3 : ℝ) / 2) := by
  rw [rpow_three_halves _ (by positivity)]
  have h : (S.card : ℝ) ≤ K := by exact_mod_cast hS
  exact mul_le_mul h (Real.sqrt_le_sqrt h) (Real.sqrt_nonneg _) (by positivity)

lemma revenue_diff_le {n : ℕ} (S : Finset (Fin n)) (w θ θ' : Fin n → ℝ) :
    |revenue S w θ - revenue S w θ'| ≤
      ∑ j ∈ S, supNorm w * |choiceProb θ S j - choiceProb θ' S j| := by
  rw [revenue_eq, revenue_eq, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_right (le_supNorm w j) (abs_nonneg _)

theorem rev_lip {n : ℕ} (K : ℕ) (S : Finset (Fin n)) (hS : S.card ≤ K)
    (w θ θ' : Fin n → ℝ) :
    |revenue S w θ - revenue S w θ'| ≤
      (1 / 4) * supNorm w * (K : ℝ) ^ ((3 : ℝ) / 2) * euclidDist θ θ' := by
  refine (revenue_diff_le S w θ θ').trans ?_
  have h1 : ∑ j ∈ S, supNorm w * |choiceProb θ S j - choiceProb θ' S j| ≤
      ∑ j ∈ S, supNorm w * ((1 / 4) * Real.sqrt (S.card : ℝ) * euclidDist θ θ') :=
    Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (lip S j hj θ θ') (supNorm_nonneg w))
  refine h1.trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hd : 0 ≤ euclidDist θ θ' := by unfold euclidDist; positivity
  have := card_mul_sqrt_le S K hS
  have hw := supNorm_nonneg w
  calc (S.card : ℝ) * (supNorm w * (1 / 4 * Real.sqrt (S.card : ℝ) * euclidDist θ θ'))
      = (1 / 4) * supNorm w * ((S.card : ℝ) * Real.sqrt (S.card : ℝ)) * euclidDist θ θ' := by ring
    _ ≤ _ := by gcongr


lemma coef_single {n : ℕ} (j : Fin n) (θ d : Fin n → ℝ) (s : ℝ) :
    coef {j} j θ d s j = Real.exp (θ j + s * d j) / (1 + Real.exp (θ j + s * d j)) -
      (Real.exp (θ j + s * d j) / (1 + Real.exp (θ j + s * d j))) ^ 2 := by
  simp [coef]; ring

lemma mvt_gen {n : ℕ} (S : Finset (Fin n)) (j : Fin n) (hj : j ∈ S) (θ d : Fin n → ℝ)
    (a b : ℝ) (hab : a < b) :
    ∃ c ∈ Set.Ioo a b, choiceProb (fun k => θ k + b * d k) S j -
        choiceProb (fun k => θ k + a * d k) S j =
      (∑ k ∈ S, coef S j θ d c k * d k) * (b - a) := by
  obtain ⟨c, hc, h⟩ := exists_hasDerivAt_eq_slope
    (fun s : ℝ => choiceProb (fun k => θ k + s * d k) S j)
    (fun s => ∑ k ∈ S, coef S j θ d s k * d k) hab
    (fun x _ => (hasDeriv_line' S j hj θ _ x).continuousAt.continuousWithinAt)
    (fun x _ => hasDeriv_line' S j hj θ _ x)
  refine ⟨c, hc, ?_⟩
  rw [h]; field_simp [(sub_pos.2 hab).ne']

lemma sig_bound (p : ℝ) : p - p ^ 2 ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1/2)]

lemma sig_pos (x : ℝ) : 0 < Real.exp x / (1 + Real.exp x) - (Real.exp x / (1 + Real.exp x)) ^ 2 := by
  have h1 := Real.exp_pos x
  have hp : 0 < Real.exp x / (1 + Real.exp x) := by positivity
  have hp1 : Real.exp x / (1 + Real.exp x) < 1 := by rw [div_lt_one (by positivity)]; linarith
  nlinarith

theorem lip_strict_one {n : ℕ} (j : Fin n) (θ θ' : Fin n → ℝ) (hd : 0 < euclidDist θ θ') :
    |choiceProb θ {j} j - choiceProb θ' {j} j| <
      (1 / 4) * Real.sqrt (({j} : Finset (Fin n)).card : ℝ) * euclidDist θ θ' := by
  set d : Fin n → ℝ := fun k => θ' k - θ k with hddef
  have hθ : (fun k => θ k + 0 * d k) = θ := by funext k; simp
  have hθ' : (fun k => θ k + 1 * d k) = θ' := by funext k; simp [hddef]
  obtain ⟨c1, hc1, h1⟩ := mvt_gen {j} j (Finset.mem_singleton_self j) θ d 0 (1/2) (by norm_num)
  obtain ⟨c2, hc2, h2⟩ := mvt_gen {j} j (Finset.mem_singleton_self j) θ d (1/2) 1 (by norm_num)
  rw [hθ] at h1; rw [hθ'] at h2
  simp only [Finset.sum_singleton, coef_single] at h1 h2
  simp only [Finset.card_singleton, Nat.cast_one, Real.sqrt_one, mul_one]
  have hdj : |d j| ≤ euclidDist θ θ' := by
    unfold euclidDist
    rw [← Real.sqrt_sq_eq_abs]
    refine Real.sqrt_le_sqrt ?_
    have := Finset.single_le_sum (f := fun k => (θ k - θ' k) ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ j)
    simp only [hddef] at this ⊢
    nlinarith [this]
  set x1 := θ j + c1 * d j
  set x2 := θ j + c2 * d j
  set a1 := Real.exp x1 / (1 + Real.exp x1) - (Real.exp x1 / (1 + Real.exp x1)) ^ 2
  set a2 := Real.exp x2 / (1 + Real.exp x2) - (Real.exp x2 / (1 + Real.exp x2)) ^ 2
  have hsum : choiceProb θ' {j} j - choiceProb θ {j} j = (a1 + a2) / 2 * d j := by
    linear_combination h1 + h2
  have ha1 := sig_bound (Real.exp x1 / (1 + Real.exp x1))
  have ha2 := sig_bound (Real.exp x2 / (1 + Real.exp x2))
  have ha1p := sig_pos x1
  have ha2p := sig_pos x2
  rw [abs_sub_comm, hsum, abs_mul]
  by_cases hdj0 : d j = 0
  · rw [hdj0]; simp; positivity
  · have hlt : a1 + a2 < 1 / 2 := by
      by_contra hcon
      have e1 : a1 = 1 / 4 := by linarith
      have e2 : a2 = 1 / 4 := by linarith
      have q1 : Real.exp x1 / (1 + Real.exp x1) = 1 / 2 := by
        have : (Real.exp x1 / (1 + Real.exp x1) - 1 / 2) ^ 2 = 0 := by nlinarith
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
        linarith
      have q2 : Real.exp x2 / (1 + Real.exp x2) = 1 / 2 := by
        have : (Real.exp x2 / (1 + Real.exp x2) - 1 / 2) ^ 2 = 0 := by nlinarith
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
        linarith
      have r1 : Real.exp x1 = 1 := by
        field_simp at q1; linarith
      have r2 : Real.exp x2 = 1 := by
        field_simp at q2; linarith
      have : x1 = x2 := Real.exp_injective (r1.trans r2.symm)
      have : c1 * d j = c2 * d j := by simp only [x1, x2] at this; linarith
      have := mul_right_cancel₀ hdj0 this
      linarith [hc1.2, hc2.1]
    rw [abs_of_pos (by linarith : 0 < (a1 + a2) / 2)]
    have hdjp : 0 < |d j| := abs_pos.2 hdj0
    calc (a1 + a2) / 2 * |d j| < (1 / 4) * |d j| := by nlinarith
      _ ≤ 1 / 4 * euclidDist θ θ' := by linarith


theorem lip_strict {n : ℕ} (S : Finset (Fin n)) (j : Fin n) (hj : j ∈ S)
    (θ θ' : Fin n → ℝ) (hd : 0 < euclidDist θ θ') :
    |choiceProb θ S j - choiceProb θ' S j| <
      (1 / 4) * Real.sqrt (S.card : ℝ) * euclidDist θ θ' := by
  have hc : 1 ≤ S.card := Finset.card_pos.2 ⟨j, hj⟩
  rcases Nat.lt_or_ge S.card 2 with h | h
  · have h1 : S.card = 1 := by omega
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h1
    have : a = j := by rw [ha] at hj; exact (Finset.mem_singleton.1 hj).symm
    subst this; rw [ha]
    exact lip_strict_one a θ θ' hd
  · exact lip_strict_two S j hj h θ θ' hd

theorem rev_lip_strict {n : ℕ} (K : ℕ) (S : Finset (Fin n)) (hS : S.card ≤ K)
    (w θ θ' : Fin n → ℝ)
    (hL : 0 < (1 / 4) * supNorm w * (K : ℝ) ^ ((3 : ℝ) / 2) * euclidDist θ θ') :
    |revenue S w θ - revenue S w θ'| <
      (1 / 4) * supNorm w * (K : ℝ) ^ ((3 : ℝ) / 2) * euclidDist θ θ' := by
  have hw := supNorm_nonneg w
  have hd0 : 0 ≤ euclidDist θ θ' := by unfold euclidDist; positivity
  have hK0 : 0 ≤ (K : ℝ) ^ ((3 : ℝ) / 2) := by positivity
  have hwp : 0 < supNorm w := by
    rcases hw.lt_or_eq with h | h
    · exact h
    · rw [← h] at hL; simp at hL
  have hdp : 0 < euclidDist θ θ' := by
    rcases hd0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hL; simp at hL
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · subst hSe
    simp only [revenue, ChoiceCDLP.MNL.mnlObjective, Finset.sum_empty, zero_div, sub_zero,
      abs_zero]
    exact hL
  refine (revenue_diff_le S w θ θ').trans_lt ?_
  have h1 : ∑ j ∈ S, supNorm w * |choiceProb θ S j - choiceProb θ' S j| <
      ∑ j ∈ S, supNorm w * ((1 / 4) * Real.sqrt (S.card : ℝ) * euclidDist θ θ') :=
    Finset.sum_lt_sum_of_nonempty hSne
      (fun j hj => mul_lt_mul_of_pos_left (lip_strict S j hj θ θ' hdp) hwp)
  refine h1.trans_le ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have := card_mul_sqrt_le S K hS
  calc (S.card : ℝ) * (supNorm w * (1 / 4 * Real.sqrt (S.card : ℝ) * euclidDist θ θ'))
      = (1 / 4) * supNorm w * ((S.card : ℝ) * Real.sqrt (S.card : ℝ)) * euclidDist θ θ' := by ring
    _ ≤ _ := by gcongr

theorem stable {n : ℕ} (K : ℕ) (w θ θ' : Fin n → ℝ) (d : ℝ)
    (hgap : HasGap w θ K d)
    (hclose : (1 / 2) * supNorm w * (K : ℝ) ^ ((3 : ℝ) / 2) * euclidDist θ θ' ≤ d)
    (S : Finset (Fin n)) (hS : IsOptimal w θ' K S) :
    IsOptimal w θ K S := by
  obtain ⟨S0, hS0mem, hS0⟩ := Finset.exists_mem_eq_sup' (feasibleSets_nonempty n K)
    (fun S => revenue S w θ)
  have hS0card : S0.card ≤ K := by simp [feasibleSets] at hS0mem; exact hS0mem
  have hopt : ∀ S' : Finset (Fin n), S'.card ≤ K → revenue S' w θ ≤ revenue S0 w θ := by
    intro S' hS'
    rw [← hS0]
    exact Finset.le_sup' (fun S => revenue S w θ) (by simp [feasibleSets]; exact hS')
  set L := (1 / 4) * supNorm w * (K : ℝ) ^ ((3 : ℝ) / 2) * euclidDist θ θ' with hLdef
  have hL0 : 0 ≤ L := by
    have := supNorm_nonneg w
    have : 0 ≤ euclidDist θ θ' := by unfold euclidDist; positivity
    positivity
  have hcmp : revenue S0 w θ' ≤ revenue S w θ' := hS.2 S0 hS0card
  refine ⟨hS.1, fun S' hS' => (hopt S' hS').trans ?_⟩
  rcases hL0.lt_or_eq with hLp | hLz
  · by_contra hno
    have hgS := hgap S hS.1 (fun h => hno ((h.2 S0 hS0card)))
    have optEq : optVal w θ K = revenue S0 w θ := hS0
    have a1 := rev_lip_strict K S hS.1 w θ θ' hLp
    have a2 := rev_lip_strict K S0 hS0card w θ θ' hLp
    rw [abs_lt] at a1 a2
    have : (1 / 2) * supNorm w * (K : ℝ) ^ ((3 : ℝ) / 2) * euclidDist θ θ' = 2 * L := by
      rw [hLdef]; ring
    linarith [a1.1, a2.2]
  · have a1 := rev_lip K S hS.1 w θ θ'
    have a2 := rev_lip K S0 hS0card w θ θ'
    rw [← hLdef, ← hLz, abs_le] at a1 a2
    linarith [a1.1, a2.2]

end DAPcpl

theorem solution {n : ℕ} (K : ℕ) (w θ θ' : Fin n → ℝ) (d : ℝ)
    (hgap : HasGap w θ K d)
    (hclose : (1 / 2) * supNorm w * (K : ℝ) ^ ((3 : ℝ) / 2) * euclidDist θ θ' ≤ d)
    (S : Finset (Fin n)) (hS : IsOptimal w θ' K S) :
    IsOptimal w θ K S :=
  DAPcpl.stable K w θ θ' d hgap hclose S hS
