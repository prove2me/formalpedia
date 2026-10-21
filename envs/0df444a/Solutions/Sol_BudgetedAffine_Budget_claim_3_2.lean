-- Prove2me | solution 1 for BudgetedAffine.Budget.claim_3_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:07:33.474491+00:00
-- url     : https://prove2.me/submissions/ecbf3ad2-afa9-4890-84da-7591fedc4072

import Mathlib
import Definitions.Def_BudgetedAffine_Budget_Model
import Definitions.Def_BudgetedAffine_Budget_Construction
import Definitions.Def_BudgetedAffine_Budget_Rescaling
import Definitions.Def_SpectralSparsify_Sampling_BernoulliSubset

set_option autoImplicit false
open Matrix BudgetedAffine.Budget SpectralSparsify.Sampling

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

lemma fup_B1 (E : Finset α) (p : α → ℝ) (hp : ∀ i ∈ E, 0 ≤ p i ∧ p i ≤ 1)
    (a : α → ℝ) (ha : ∀ i ∈ E, 0 ≤ a i ∧ a i ≤ 1) (s : ℝ)
    (hE : ∑ i ∈ E, p i * a i ≤ s) (δ : ℝ) (hδ : 0 < δ) :
    prob E p (fun T => (1 + δ) * s ≤ ∑ i ∈ T, a i) ≤
      (Real.exp δ / (1 + δ) ^ (1 + δ)) ^ s := by
  have h1 : 0 < 1 + δ := by linarith
  have ht : 0 ≤ Real.log (1 + δ) := Real.log_nonneg (by linarith)
  have := fup_upper E p hp a ha s hE ((1 + δ) * s) (Real.log (1 + δ)) ht
  refine this.trans (le_of_eq ?_)
  rw [Real.rpow_def_of_pos (div_pos (Real.exp_pos _) (Real.rpow_pos_of_pos h1 _)),
    Real.log_div (Real.exp_pos _).ne' (Real.rpow_pos_of_pos h1 _).ne', Real.log_exp,
    Real.log_rpow h1, ← Real.exp_add, Real.exp_log h1]
  congr 1
  ring

open scoped Classical in
lemma fup_union {ι : Type*} (E : Finset α) (p : α → ℝ) (hp : ∀ i ∈ E, 0 ≤ p i ∧ p i ≤ 1)
    (S : Finset ι) (Q : ι → Finset α → Prop) :
    prob E p (fun T => ∃ j ∈ S, Q j T) ≤ ∑ j ∈ S, prob E p (Q j) := by
  unfold prob
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro T hT
  have hT' := Finset.mem_powerset.mp hT
  have hw := fup_outcomeProb_nonneg E p hp T hT'
  split_ifs with h
  · obtain ⟨j, hj, hQ⟩ := h
    have := Finset.single_le_sum (f := fun j => if Q j T then outcomeProb E p T else 0)
      (fun k _ => by split_ifs <;> simp [hw]) hj
    simp only [hQ, if_true] at this
    exact this
  · exact Finset.sum_nonneg (fun k _ => by split_ifs <;> simp [hw])

lemma fup_prob_false (E : Finset α) (p : α → ℝ) : prob E p (fun _ => False) = 0 := by
  simp [prob]

lemma fup_sum_split (J T : Finset α) (hT : T ⊆ J) (a f : α → ℝ) (c : ℝ) :
    ∑ i ∈ J, a i * (c * (f i + if i ∈ T then 1 else 0)) =
      c * (∑ i ∈ J, a i * f i + ∑ i ∈ T, a i) := by
  have e : ∑ i ∈ T, a i = ∑ i ∈ J, if i ∈ T then a i else 0 := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hT]
  rw [e, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  by_cases h : i ∈ T <;> simp [h] <;> ring

end chern

theorem solution {m n : ℕ} (hn : 3 ≤ n) (B : Matrix (Fin m) (Fin n) ℝ) (d : Fin n → ℝ)
    (J : Finset (Fin m)) (γ : ℝ) (w : Fin m → ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (hd : 0 ≤ d) (hγ : 0 < γ) (hw : ∀ i ∈ J, 0 < w i ∧ w i ≤ 1)
    (hcond1 : ∀ i ∈ J,
      ((4 * γ * (Real.log n / Real.log (Real.log n)) * w i : ℝ) : EReal) <
        coverCost B d (Pi.single i 1))
    (zs : Fin m → ℝ) (hzs : DualFeasible (BHat B w J) (dHat B d w J (beta n) γ) J zs) :
    1 - n * (Real.exp (beta n / 2 - 2) / (1 + (beta n / 2 - 2)) ^ (1 + (beta n / 2 - 2))) ≤
      prob J (fun i => zs i - ⌊zs i⌋)
        (fun T => DualFeasible (BHat B w J) (dHat B d w J (beta n) γ) J
          (fun i => 2 * ((⌊zs i⌋ : ℝ) + if i ∈ T then 1 else 0) / beta n)) := by
  obtain ⟨hzs0, hzsj⟩ := hzs
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog1 : 1 < Real.log n := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hll : 0 < Real.log (Real.log n) := Real.log_pos hlog1
  have hlogle := Real.log_le_sub_one_of_pos (by linarith : 0 < Real.log n)
  have hη4 : 4 < beta n := by
    unfold beta
    rw [lt_div_iff₀ hll]
    nlinarith
  have hηeq : beta n = 4 * (Real.log n / Real.log (Real.log n)) := by
    unfold beta; ring
  generalize hη : beta n = η at *
  have hη0 : 0 < η := by linarith
  have hδ : 0 < η / 2 - 2 := by linarith
  generalize hδd : η / 2 - 2 = δ at *
  have h1δ : 0 < 1 + δ := by linarith
  have hb0 : 0 < Real.exp δ / (1 + δ) ^ (1 + δ) :=
    div_pos (Real.exp_pos _) (Real.rpow_pos_of_pos h1δ _)
  have hb1 : Real.exp δ / (1 + δ) ^ (1 + δ) ≤ 1 := by
    rw [div_le_one (Real.rpow_pos_of_pos h1δ _), Real.rpow_def_of_pos h1δ]
    apply Real.exp_le_exp.mpr
    have := Real.one_sub_inv_le_log_of_pos h1δ
    have h2 : (1 + δ) * (1 - (1 + δ)⁻¹) = δ := by field_simp; ring
    nlinarith
  have hfl : ∀ i ∈ J, (0 : ℝ) ≤ ⌊zs i⌋ := fun i hi => by
    exact_mod_cast Int.floor_nonneg.mpr (hzs0 i hi)
  have hp : ∀ i ∈ J, 0 ≤ (fun i => zs i - (⌊zs i⌋ : ℝ)) i ∧
      (fun i => zs i - (⌊zs i⌋ : ℝ)) i ≤ 1 := by
    intro i _
    refine ⟨sub_nonneg.2 (Int.floor_le _), ?_⟩
    have := Int.lt_floor_add_one (zs i)
    simp only; linarith
  have hcol : ∀ j : Fin n, prob J (fun i => zs i - ⌊zs i⌋)
      (fun T => dHat B d w J η γ j <
        ∑ i ∈ J, BHat B w J i j * (2 * ((⌊zs i⌋ : ℝ) + if i ∈ T then 1 else 0) / η)) ≤
      Real.exp δ / (1 + δ) ^ (1 + δ) := by
    intro j
    by_cases hcm : colMax B w J j = 0
    · have hD : dHat B d w J η γ j = 0 := by simp [dHat, hcm]
      have hBh : ∀ i, BHat B w J i j = 0 := by intro i; simp [BHat, hcm]
      calc _ ≤ prob J (fun i => zs i - ⌊zs i⌋) (fun _ => False) := by
            apply fup_prob_mono J _ hp
            intro T _ h
            rw [hD] at h
            simp [hBh] at h
        _ = 0 := fup_prob_false _ _
        _ ≤ _ := hb0.le
    · have hM0 : 0 ≤ colMax B w J j := by
        unfold colMax
        apply Real.iSup_nonneg
        intro k
        exact mul_nonneg (hw k k.2).1.le (hB _ _)
      have hMpos : 0 < colMax B w J j := lt_of_le_of_ne hM0 (Ne.symm hcm)
      have hle : ∀ i ∈ J, w i * B i j ≤ colMax B w J j := fun i hi =>
        le_ciSup (f := fun k : {x // x ∈ J} => w k * B k j) (Finite.bddAbove_range _) ⟨i, hi⟩
      have hcover : ∀ i ∈ J, γ * η * (w i * B i j) ≤ d j := by
        intro i hi
        by_cases hBij : B i j = 0
        · simp [hBij]; exact hd j
        · have hBpos : 0 < B i j := lt_of_le_of_ne (hB i j) (Ne.symm hBij)
          have hc := hcond1 i hi
          have hle2 : coverCost B d (Pi.single i 1) ≤
              ((d ⬝ᵥ (Pi.single j (1 / B i j) : Fin n → ℝ) : ℝ) : EReal) := by
            unfold coverCost
            apply iInf₂_le (f := fun (y : Fin n → ℝ) (_ : 0 ≤ y ∧ (Pi.single i 1 : Fin m → ℝ) ≤ B *ᵥ y) =>
              ((d ⬝ᵥ y : ℝ) : EReal)) (Pi.single j (1 / B i j))
            refine ⟨?_, ?_⟩
            · intro k
              by_cases hk : k = j
              · subst hk; simp; exact hBpos.le
              · simp [hk]
            · intro k
              have e : (B *ᵥ Pi.single j (1 / B i j) : Fin m → ℝ) k = B k j * (1 / B i j) := by
                simp [Matrix.mulVec, dotProduct, Pi.single_apply]
              rw [e]
              by_cases hk : k = i
              · subst hk
                have : B k j * (1 / B k j) = 1 := by field_simp
                rw [this, Pi.single_eq_same]
              · simp [hk]
                exact mul_nonneg (hB k j) (by positivity)
          have hc2 := lt_of_lt_of_le hc hle2
          rw [dotProduct_single, EReal.coe_lt_coe_iff] at hc2
          have h3 := mul_lt_mul_of_pos_right hc2 hBpos
          have e : d j * (1 / B i j) * B i j = d j := by field_simp
          rw [e] at h3
          calc γ * η * (w i * B i j)
              = 4 * γ * (Real.log n / Real.log (Real.log n)) * w i * B i j := by
                rw [hηeq]; ring
            _ ≤ d j := h3.le
      have hdhat : 1 ≤ dHat B d w J η γ j := by
        have hMle : colMax B w J j ≤ d j / (γ * η) := by
          unfold colMax
          apply Real.iSup_le
          · intro k
            rw [le_div_iff₀ (by positivity)]
            have := hcover k k.2
            linarith [this]
          · exact div_nonneg (hd j) (by positivity)
        unfold dHat
        rw [one_le_div (by positivity)]
        rw [le_div_iff₀ (by positivity)] at hMle
        nlinarith [hMle]
      have ha : ∀ i ∈ J, 0 ≤ BHat B w J i j ∧ BHat B w J i j ≤ 1 := by
        intro i hi
        simp only [BHat, Matrix.of_apply, if_pos hi]
        exact ⟨div_nonneg (mul_nonneg (hw i hi).1.le (hB _ _)) hM0,
          (div_le_one hMpos).mpr (hle i hi)⟩
      have hF : ∑ i ∈ J, BHat B w J i j * (⌊zs i⌋ : ℝ) ≤ ∑ i ∈ J, BHat B w J i j * zs i :=
        Finset.sum_le_sum (fun i hi =>
          mul_le_mul_of_nonneg_left (Int.floor_le _) (ha i hi).1)
      have hE : ∑ i ∈ J, (zs i - (⌊zs i⌋ : ℝ)) * BHat B w J i j ≤ dHat B d w J η γ j := by
        have e : ∑ i ∈ J, (zs i - (⌊zs i⌋ : ℝ)) * BHat B w J i j =
            ∑ i ∈ J, BHat B w J i j * zs i - ∑ i ∈ J, BHat B w J i j * (⌊zs i⌋ : ℝ) := by
          rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; ring
        have hF0 : 0 ≤ ∑ i ∈ J, BHat B w J i j * (⌊zs i⌋ : ℝ) :=
          Finset.sum_nonneg (fun i hi => mul_nonneg (ha i hi).1 (hfl i hi))
        linarith [hzsj j]
      have hB1 := fup_B1 J (fun i => zs i - (⌊zs i⌋ : ℝ)) hp (fun i => BHat B w J i j) ha
        (dHat B d w J η γ j) hE δ hδ
      calc _ ≤ prob J (fun i => zs i - ⌊zs i⌋)
            (fun T => (1 + δ) * dHat B d w J η γ j ≤ ∑ i ∈ T, BHat B w J i j) := by
            apply fup_prob_mono J _ hp
            intro T hT h
            simp only [show ∀ x : ℝ, 2 * x / η = 2 / η * x from fun x => by ring] at h
            rw [fup_sum_split J T hT (fun i => BHat B w J i j) (fun i => (⌊zs i⌋ : ℝ)) (2 / η)] at h
            have hFle := hF.trans (hzsj j)
            have key : 2 / η * (∑ i ∈ J, BHat B w J i j * (⌊zs i⌋ : ℝ) + ∑ i ∈ T, BHat B w J i j) * η =
                2 * (∑ i ∈ J, BHat B w J i j * (⌊zs i⌋ : ℝ) + ∑ i ∈ T, BHat B w J i j) := by
              field_simp
            have h2 := mul_lt_mul_of_pos_right h hη0
            rw [key] at h2
            rw [← hδd]
            nlinarith
        _ ≤ (Real.exp δ / (1 + δ) ^ (1 + δ)) ^ (dHat B d w J η γ j) := hB1
        _ ≤ (Real.exp δ / (1 + δ) ^ (1 + δ)) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge hb0 hb1 hdhat
        _ = _ := Real.rpow_one _
  have hP := fup_prob_add J (fun i => zs i - ⌊zs i⌋) (fun T => DualFeasible (BHat B w J)
    (dHat B d w J η γ) J (fun i => 2 * ((⌊zs i⌋ : ℝ) + if i ∈ T then 1 else 0) / η))
  have hU := fup_union J (fun i => zs i - ⌊zs i⌋) hp (Finset.univ : Finset (Fin n))
    (fun j T => dHat B d w J η γ j <
      ∑ i ∈ J, BHat B w J i j * (2 * ((⌊zs i⌋ : ℝ) + if i ∈ T then 1 else 0) / η))
  have hmono := fup_prob_mono J (fun i => zs i - ⌊zs i⌋) hp
    (fun T => ¬ DualFeasible (BHat B w J) (dHat B d w J η γ) J
      (fun i => 2 * ((⌊zs i⌋ : ℝ) + if i ∈ T then 1 else 0) / η))
    (fun T => ∃ j ∈ (Finset.univ : Finset (Fin n)), dHat B d w J η γ j <
      ∑ i ∈ J, BHat B w J i j * (2 * ((⌊zs i⌋ : ℝ) + if i ∈ T then 1 else 0) / η)) (by
      intro T hT h
      by_contra hcon
      apply h
      refine ⟨?_, ?_⟩
      · intro i hi
        have := hfl i hi
        have h0 : (0 : ℝ) ≤ ((⌊zs i⌋ : ℝ) + if i ∈ T then 1 else 0) := by
          split_ifs <;> linarith
        positivity
      · intro j
        by_contra hj
        exact hcon ⟨j, Finset.mem_univ _, not_le.mp hj⟩)
  have hsum : ∑ j ∈ (Finset.univ : Finset (Fin n)), prob J (fun i => zs i - ⌊zs i⌋)
      (fun T => dHat B d w J η γ j <
        ∑ i ∈ J, BHat B w J i j * (2 * ((⌊zs i⌋ : ℝ) + if i ∈ T then 1 else 0) / η)) ≤
      ∑ j : Fin n, Real.exp δ / (1 + δ) ^ (1 + δ) :=
    Finset.sum_le_sum (fun j _ => hcol j)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  linarith
