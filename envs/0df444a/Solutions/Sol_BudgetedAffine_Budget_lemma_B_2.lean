-- Prove2me | solution 1 for BudgetedAffine.Budget.lemma_B_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:01:35.515081+00:00
-- url     : https://prove2.me/submissions/696a0765-5161-4607-ba7b-d71064150a74

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

lemma fup_xlogx (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) : (x - x⁻¹) / 2 ≤ Real.log x := by
  set g : ℝ → ℝ := fun y => Real.log y - (y - y⁻¹) / 2 with hg
  have hd : ∀ y : ℝ, 0 < y → HasDerivAt g (y⁻¹ - (1 - -(y ^ 2)⁻¹) / 2) y := by
    intro y hy
    exact (Real.hasDerivAt_log hy.ne').sub
      (((hasDerivAt_id y).sub (hasDerivAt_inv hy.ne')).div_const 2)
  have hanti : AntitoneOn g (Set.Ioc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 1)
    · intro y hy
      exact (hd y hy.1).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ioc] at hy
      exact (hd y hy.1).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ioc] at hy
      rw [(hd y hy.1).deriv]
      have hy0 := hy.1
      have : y⁻¹ - (1 - -(y ^ 2)⁻¹) / 2 = -((1 - y⁻¹) ^ 2) / 2 := by
        field_simp
        ring
      rw [this]
      nlinarith [sq_nonneg (1 - y⁻¹)]
  have := hanti ⟨hx0, hx1⟩ ⟨by norm_num, le_rfl⟩ hx1
  simp only [hg, Real.log_one, inv_one, sub_self, zero_div, sub_zero] at this
  linarith

lemma fup_B2 (E : Finset α) (p : α → ℝ) (hp : ∀ i ∈ E, 0 ≤ p i ∧ p i ≤ 1)
    (a : α → ℝ) (ha : ∀ i ∈ E, 0 ≤ a i ∧ a i ≤ 1) (lam : ℝ) (hlam : 0 ≤ lam)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - Real.exp (-(δ ^ 2 * (lam + ∑ i ∈ E, p i * a i) / 2)) ≤
      prob E p (fun T => (1 - δ) * (lam + ∑ i ∈ E, p i * a i) < lam + ∑ i ∈ T, a i) := by
  set m : ℝ := ∑ i ∈ E, p i * a i with hm
  have hm0 : 0 ≤ m := Finset.sum_nonneg (fun i hi => mul_nonneg (hp i hi).1 (ha i hi).1)
  have hx : 0 < 1 - δ := by linarith
  set t : ℝ := -Real.log (1 - δ) with ht
  have hlog : Real.log (1 - δ) ≤ -δ := by
    have := Real.log_le_sub_one_of_pos hx; linarith
  have ht1 : δ ≤ t := by rw [ht]; linarith
  have ht0 : 0 ≤ t := by linarith
  have het : Real.exp (-t) = 1 - δ := by rw [ht, neg_neg, Real.exp_log hx]
  have hP := fup_prob_add E p (fun T => (1 - δ) * (lam + m) < lam + ∑ i ∈ T, a i)
  have hlow := fup_lower E p hp a ha lam ((1 - δ) * (lam + m)) t ht0
  have hmono := fup_prob_mono E p hp (fun T => ¬ ((1 - δ) * (lam + m) < lam + ∑ i ∈ T, a i))
    (fun T => lam + ∑ i ∈ T, a i ≤ (1 - δ) * (lam + m)) (fun T _ h => not_lt.mp h)
  have hxl := fup_xlogx (1 - δ) hx (by linarith)
  have hxl2 : t * (1 - δ) - δ ≤ -(δ ^ 2 / 2) := by
    have h1 := mul_le_mul_of_nonneg_left hxl hx.le
    have h2 : (1 - δ) * (((1 - δ) - (1 - δ)⁻¹) / 2) = ((1 - δ) ^ 2 - 1) / 2 := by
      field_simp
    rw [h2] at h1
    rw [ht]
    nlinarith
  have hexp : Real.exp (t * ((1 - δ) * (lam + m) - lam)) *
      Real.exp (-((1 - Real.exp (-t)) * m)) ≤ Real.exp (-(δ ^ 2 * (lam + m) / 2)) := by
    rw [← Real.exp_add, het]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hlam (by nlinarith : 0 ≤ t * δ - δ ^ 2 / 2),
      mul_nonneg hm0 (by linarith : 0 ≤ -(δ ^ 2 / 2) - (t * (1 - δ) - δ))]
  linarith

end chern

theorem solution (r : ℕ) (p a : Fin r → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (ha : ∀ i, 0 < a i ∧ a i ≤ 1) (lam : ℝ) (hlam : 0 ≤ lam) (δ : ℝ) (hδ : 0 < δ)
    (hδ1 : δ < 1) :
    1 - Real.exp (-(δ ^ 2 * expect Finset.univ p (fun T => lam + ∑ i ∈ T, a i) / 2)) ≤
      prob Finset.univ p (fun T =>
        (1 - δ) * expect Finset.univ p (fun T' => lam + ∑ i ∈ T', a i) < lam + ∑ i ∈ T, a i) := by
  simp only [fup_expect_add_const, fup_expect_sum]
  exact fup_B2 Finset.univ p (fun i _ => hp i) a (fun i _ => ⟨(ha i).1.le, (ha i).2⟩) lam hlam δ hδ hδ1
