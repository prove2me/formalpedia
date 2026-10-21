-- Prove2me | solution 1 for BudgetedAffine.Budget.lemma_B_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:00:14.676996+00:00
-- url     : https://prove2.me/submissions/cdc37238-cc46-45d9-abdc-3e138a977667

import Mathlib
import Definitions.Def_SpectralSparsify_Sampling_BernoulliSubset

set_option autoImplicit false
open SpectralSparsify.Sampling

section chern
variable {α : Type*} [DecidableEq α]

lemma fup_outcomeProb_nonneg (E : Finset α) (p : α → ℝ) (hp : ∀ i ∈ E, 0 ≤ p i ∧ p i ≤ 1)
    (T : Finset α) (hT : T ⊆ E) : 0 ≤ outcomeProb E p T := by
  unfold outcomeProb
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun i hi => (hp i (hT hi)).1)
  · exact Finset.prod_nonneg (fun i hi => by
      have := (hp i (Finset.mem_sdiff.mp hi).1).2; linarith)

lemma fup_expect_prod (E : Finset α) (p g : α → ℝ) :
    expect E p (fun T => ∏ i ∈ T, g i) = ∏ i ∈ E, (p i * g i + (1 - p i)) := by
  have := Finset.prod_add (fun i => p i * g i) (fun i => 1 - p i) E
  refine Eq.trans ?_ this.symm
  unfold expect outcomeProb
  apply Finset.sum_congr rfl
  intro T _
  rw [Finset.prod_mul_distrib]
  ring

lemma fup_expect_one (E : Finset α) (p : α → ℝ) : expect E p (fun _ => (1 : ℝ)) = 1 := by
  have := fup_expect_prod E p (fun _ => 1)
  simpa using this

lemma fup_prob_le_expect (E : Finset α) (p : α → ℝ) (hp : ∀ i ∈ E, 0 ≤ p i ∧ p i ≤ 1)
    (P : Finset α → Prop) (φ : Finset α → ℝ) (hφ0 : ∀ T ⊆ E, 0 ≤ φ T)
    (hφ1 : ∀ T ⊆ E, P T → 1 ≤ φ T) : prob E p P ≤ expect E p φ := by
  unfold prob expect
  apply Finset.sum_le_sum
  intro T hT
  have hT' := Finset.mem_powerset.mp hT
  have hw := fup_outcomeProb_nonneg E p hp T hT'
  split_ifs with h
  · nlinarith [hφ1 T hT' h]
  · exact mul_nonneg hw (hφ0 T hT')

lemma fup_prob_mono (E : Finset α) (p : α → ℝ) (hp : ∀ i ∈ E, 0 ≤ p i ∧ p i ≤ 1)
    (P Q : Finset α → Prop) (h : ∀ T ⊆ E, P T → Q T) : prob E p P ≤ prob E p Q := by
  unfold prob
  apply Finset.sum_le_sum
  intro T hT
  have hT' := Finset.mem_powerset.mp hT
  have hw := fup_outcomeProb_nonneg E p hp T hT'
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (h T hT' h1) h2
  · exact hw
  · exact le_rfl

lemma fup_prob_add (E : Finset α) (p : α → ℝ) (P : Finset α → Prop) :
    prob E p P + prob E p (fun T => ¬ P T) = 1 := by
  have h1 := fup_expect_one E p
  unfold expect at h1
  simp only [mul_one] at h1
  unfold prob
  rw [← Finset.sum_add_distrib, ← h1]
  apply Finset.sum_congr rfl
  intro T _
  by_cases h : P T <;> simp [h]

lemma fup_expect_mul_const (E : Finset α) (p : α → ℝ) (k : ℝ) (X : Finset α → ℝ) :
    expect E p (fun T => k * X T) = k * expect E p X := by
  unfold expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  ring

lemma fup_expect_add_const (E : Finset α) (p : α → ℝ) (k : ℝ) (X : Finset α → ℝ) :
    expect E p (fun T => k + X T) = k + expect E p X := by
  have h1 := fup_expect_one E p
  unfold expect at h1 ⊢
  simp only [mul_one] at h1
  calc ∑ T ∈ E.powerset, outcomeProb E p T * (k + X T)
      = k * ∑ T ∈ E.powerset, outcomeProb E p T + ∑ T ∈ E.powerset, outcomeProb E p T * X T := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro T _; ring
    _ = _ := by rw [h1, mul_one]

lemma fup_expect_mem (E : Finset α) (p : α → ℝ) (i : α) :
    expect E p (fun T => if i ∈ T then (1 : ℝ) else 0) = p i ∨ i ∉ E := by
  by_cases hi : i ∈ E
  · left
    have h1 := fup_expect_prod E p (fun j => if j = i then (0 : ℝ) else 1)
    have h2 : ∀ T : Finset α, ∏ j ∈ T, (if j = i then (0 : ℝ) else 1) = if i ∈ T then 0 else 1 := by
      intro T
      by_cases hT : i ∈ T
      · rw [Finset.prod_eq_zero hT (by simp)]; simp [hT]
      · rw [Finset.prod_eq_one (fun j hj => by
          have : j ≠ i := fun h => hT (h ▸ hj)
          simp [this])]
        simp [hT]
    simp only [h2] at h1
    have h3 : ∏ j ∈ E, (p j * (if j = i then (0 : ℝ) else 1) + (1 - p j)) = 1 - p i := by
      rw [Finset.prod_eq_single i]
      · simp
      · intro j _ hj; simp [hj]
      · intro h; exact absurd hi h
    rw [h3] at h1
    have h4 := fup_expect_one E p
    unfold expect at h1 h4 ⊢
    simp only [mul_one] at h4
    have h5 : ∑ T ∈ E.powerset, outcomeProb E p T * (if i ∈ T then (1 : ℝ) else 0)
        + ∑ T ∈ E.powerset, outcomeProb E p T * (if i ∈ T then (0 : ℝ) else 1) = 1 := by
      calc _ = ∑ T ∈ E.powerset, outcomeProb E p T := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl; intro T _
            by_cases h : i ∈ T <;> simp [h]
        _ = 1 := h4
    linarith
  · right; exact hi

lemma fup_expect_sum (E : Finset α) (p : α → ℝ) (a : α → ℝ) :
    expect E p (fun T => ∑ i ∈ T, a i) = ∑ i ∈ E, p i * a i := by
  have key : ∀ T ∈ E.powerset, outcomeProb E p T * ∑ i ∈ T, a i =
      ∑ i ∈ E, a i * (outcomeProb E p T * (if i ∈ T then (1 : ℝ) else 0)) := by
    intro T hT
    have hT' := Finset.mem_powerset.mp hT
    have : ∑ i ∈ T, a i = ∑ i ∈ E, if i ∈ T then a i else 0 := by
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hT']
    rw [this, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    by_cases h : i ∈ T <;> simp [h]; ring
  unfold expect
  rw [Finset.sum_congr rfl key, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have := fup_expect_mem E p i
  rcases this with h | h
  · unfold expect at h
    rw [← Finset.mul_sum, h]; ring
  · exact absurd hi h

lemma fup_exp_up (t a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Real.exp (t * a) - 1 ≤ a * (Real.exp t - 1) := by
  have := convexOn_exp.2 (Set.mem_univ t) (Set.mem_univ 0) ha0 (sub_nonneg.2 ha1) (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at this
  rw [mul_comm t a]
  nlinarith

lemma fup_exp_low (t a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    a * (1 - Real.exp (-t)) ≤ 1 - Real.exp (-(t * a)) := by
  have := convexOn_exp.2 (Set.mem_univ (-t)) (Set.mem_univ 0) ha0 (sub_nonneg.2 ha1) (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at this
  have e : -(t * a) = a * (-t) := by ring
  rw [e]
  nlinarith

lemma fup_upper (E : Finset α) (p : α → ℝ) (hp : ∀ i ∈ E, 0 ≤ p i ∧ p i ≤ 1)
    (a : α → ℝ) (ha : ∀ i ∈ E, 0 ≤ a i ∧ a i ≤ 1) (s : ℝ)
    (hE : ∑ i ∈ E, p i * a i ≤ s) (c t : ℝ) (ht : 0 ≤ t) :
    prob E p (fun T => c ≤ ∑ i ∈ T, a i) ≤
      Real.exp (-(t * c)) * Real.exp (s * (Real.exp t - 1)) := by
  have hexp : 0 ≤ Real.exp t - 1 := by
    have := Real.add_one_le_exp t; linarith [Real.exp_pos t, Real.add_one_le_exp t,
      Real.one_le_exp ht]
  calc prob E p (fun T => c ≤ ∑ i ∈ T, a i)
      ≤ expect E p (fun T => Real.exp (-(t * c)) * ∏ i ∈ T, Real.exp (t * a i)) := by
        apply fup_prob_le_expect E p hp
        · intro T _
          exact mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg (fun i _ => (Real.exp_pos _).le))
        · intro T _ hc
          rw [← Real.exp_sum, ← Finset.mul_sum, ← Real.exp_add]
          apply Real.one_le_exp
          nlinarith
    _ = Real.exp (-(t * c)) * ∏ i ∈ E, (p i * Real.exp (t * a i) + (1 - p i)) := by
        rw [fup_expect_mul_const, fup_expect_prod]
    _ ≤ Real.exp (-(t * c)) * Real.exp (s * (Real.exp t - 1)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        calc ∏ i ∈ E, (p i * Real.exp (t * a i) + (1 - p i))
            ≤ ∏ i ∈ E, Real.exp (p i * a i * (Real.exp t - 1)) := by
              apply Finset.prod_le_prod
              · intro i hi
                have := hp i hi
                have := Real.exp_pos (t * a i)
                nlinarith
              · intro i hi
                have h1 := hp i hi
                have h2 := ha i hi
                have h3 := fup_exp_up t (a i) h2.1 h2.2
                have h4 := Real.add_one_le_exp (p i * (Real.exp (t * a i) - 1))
                have h5 : p i * (Real.exp (t * a i) - 1) ≤ p i * a i * (Real.exp t - 1) := by
                  have := mul_le_mul_of_nonneg_left h3 h1.1
                  linarith
                have h6 := Real.exp_le_exp.mpr h5
                nlinarith
          _ = Real.exp (∑ i ∈ E, p i * a i * (Real.exp t - 1)) := by rw [Real.exp_sum]
          _ ≤ Real.exp (s * (Real.exp t - 1)) := by
              apply Real.exp_le_exp.mpr
              rw [← Finset.sum_mul]
              exact mul_le_mul_of_nonneg_right hE hexp

lemma fup_lower (E : Finset α) (p : α → ℝ) (hp : ∀ i ∈ E, 0 ≤ p i ∧ p i ≤ 1)
    (a : α → ℝ) (ha : ∀ i ∈ E, 0 ≤ a i ∧ a i ≤ 1) (lam c t : ℝ) (ht : 0 ≤ t) :
    prob E p (fun T => lam + ∑ i ∈ T, a i ≤ c) ≤
      Real.exp (t * (c - lam)) * Real.exp (-((1 - Real.exp (-t)) * ∑ i ∈ E, p i * a i)) := by
  have hexp : 0 ≤ 1 - Real.exp (-t) := by
    have : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  calc prob E p (fun T => lam + ∑ i ∈ T, a i ≤ c)
      ≤ expect E p (fun T => Real.exp (t * (c - lam)) * ∏ i ∈ T, Real.exp (-(t * a i))) := by
        apply fup_prob_le_expect E p hp
        · intro T _
          exact mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg (fun i _ => (Real.exp_pos _).le))
        · intro T _ hc
          rw [← Real.exp_sum, Finset.sum_neg_distrib, ← Finset.mul_sum, ← Real.exp_add]
          apply Real.one_le_exp
          nlinarith [mul_nonneg ht (sub_nonneg.2 hc)]
    _ = Real.exp (t * (c - lam)) * ∏ i ∈ E, (p i * Real.exp (-(t * a i)) + (1 - p i)) := by
        rw [fup_expect_mul_const, fup_expect_prod]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        calc ∏ i ∈ E, (p i * Real.exp (-(t * a i)) + (1 - p i))
            ≤ ∏ i ∈ E, Real.exp (-(p i * a i * (1 - Real.exp (-t)))) := by
              apply Finset.prod_le_prod
              · intro i hi
                have := hp i hi
                have := Real.exp_pos (-(t * a i))
                nlinarith
              · intro i hi
                have h1 := hp i hi
                have h2 := ha i hi
                have h3 := fup_exp_low t (a i) h2.1 h2.2
                have h4 := Real.add_one_le_exp (-(p i * (1 - Real.exp (-(t * a i)))))
                have h5 : -(p i * (1 - Real.exp (-(t * a i)))) ≤ -(p i * a i * (1 - Real.exp (-t))) := by
                  have := mul_le_mul_of_nonneg_left h3 h1.1
                  linarith
                have h6 := Real.exp_le_exp.mpr h5
                nlinarith
          _ = Real.exp (∑ i ∈ E, -(p i * a i * (1 - Real.exp (-t)))) := by rw [Real.exp_sum]
          _ = _ := by
              congr 1
              rw [Finset.sum_neg_distrib, ← Finset.sum_mul]
              ring

end chern

theorem solution (r : ℕ) (p a : Fin r → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (s : ℝ) (hs : 0 < s)
    (hE : expect Finset.univ p (fun T => ∑ i ∈ T, a i) ≤ s) (δ : ℝ) (hδ : 0 < δ) :
    prob Finset.univ p (fun T => (1 + δ) * s ≤ ∑ i ∈ T, a i) ≤
      (Real.exp δ / (1 + δ) ^ (1 + δ)) ^ s := by
  rw [fup_expect_sum] at hE
  have h1 : 0 < 1 + δ := by linarith
  have ht : 0 ≤ Real.log (1 + δ) := Real.log_nonneg (by linarith)
  have := fup_upper Finset.univ p (fun i _ => hp i) a (fun i _ => ha i) s hE ((1 + δ) * s)
    (Real.log (1 + δ)) ht
  refine this.trans (le_of_eq ?_)
  rw [Real.rpow_def_of_pos (div_pos (Real.exp_pos _) (Real.rpow_pos_of_pos h1 _)),
    Real.log_div (Real.exp_pos _).ne' (Real.rpow_pos_of_pos h1 _).ne', Real.log_exp,
    Real.log_rpow h1, ← Real.exp_add, Real.exp_log h1]
  congr 1
  ring
