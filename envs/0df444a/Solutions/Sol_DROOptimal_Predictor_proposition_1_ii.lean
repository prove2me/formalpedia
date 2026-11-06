-- Prove2me | solution 1 for DROOptimal.Predictor.proposition_1_ii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T09:52:39.068969+00:00
-- url     : https://prove2.me/submissions/aaff7552-eda4-4dab-ace9-b871359f8462

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting
import Definitions.Def_DROOptimal_Predictor_Problem5

open DROOptimal.Predictor

namespace DROm4P1ii

/-- a log(a/b) ≥ a − b. -/
lemma mul_log_div_ge_sub (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    a - b ≤ a * Real.log (a / b) := by
  rcases ha.eq_or_lt with h | h
  · subst h; simp; linarith
  · have h1 := Real.one_sub_inv_le_log_of_pos (div_pos h hb)
    rw [inv_div] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 h.le
    have h3 : a * (b / a) = b := by field_simp
    rw [mul_sub, mul_one, h3] at h2
    exact h2

/-- Tangent bound: w·a log(a/b) ≥ w·a log λ + w·a − λ w b. -/
lemma tangent (w a b l : ℝ) (hw : 0 ≤ w) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b = 0 → a = 0)
    (hl : 0 < l) :
    w * a * Real.log l + w * a - l * (w * b) ≤ w * (a * Real.log (a / b)) := by
  rcases hb.eq_or_lt with hb0 | hb0
  · have ha0 := hab hb0.symm
    rw [ha0, ← hb0]; simp
  · rcases ha.eq_or_lt with ha0 | ha0
    · rw [← ha0]; simp; positivity
    · have h1 := mul_log_div_ge_sub a (l * b) ha (mul_pos hl hb0)
      have h2 : Real.log (a / (l * b)) = Real.log (a / b) - Real.log l := by
        rw [Real.log_div ha0.ne' (mul_pos hl hb0).ne', Real.log_mul hl.ne' hb0.ne',
          Real.log_div ha0.ne' hb0.ne']; ring
      rw [h2] at h1
      nlinarith [mul_le_mul_of_nonneg_left h1 hw]

/-- Two-point log-sum inequality. -/
lemma logsum (w1 w2 a1 a2 b1 b2 : ℝ) (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2)
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2)
    (h1 : b1 = 0 → a1 = 0) (h2 : b2 = 0 → a2 = 0) :
    (w1 * a1 + w2 * a2) * Real.log ((w1 * a1 + w2 * a2) / (w1 * b1 + w2 * b2)) ≤
      w1 * (a1 * Real.log (a1 / b1)) + w2 * (a2 * Real.log (a2 / b2)) := by
  set A := w1 * a1 + w2 * a2 with hA
  set B := w1 * b1 + w2 * b2 with hB
  have hA0 : 0 ≤ A := by positivity
  rcases hA0.eq_or_lt with hA0 | hApos
  · have e1 : w1 * a1 = 0 := by nlinarith [mul_nonneg hw1 ha1, mul_nonneg hw2 ha2]
    have e2 : w2 * a2 = 0 := by nlinarith [mul_nonneg hw1 ha1, mul_nonneg hw2 ha2]
    rw [← hA0, zero_mul, ← mul_assoc, ← mul_assoc, e1, e2]; simp
  · have hBpos : 0 < B := by
      rcases (show 0 ≤ B by positivity).eq_or_lt with hB0 | hB0
      · exfalso
        have f1 : w1 * b1 = 0 := by nlinarith [mul_nonneg hw1 hb1, mul_nonneg hw2 hb2]
        have f2 : w2 * b2 = 0 := by nlinarith [mul_nonneg hw1 hb1, mul_nonneg hw2 hb2]
        have g1 : w1 * a1 = 0 := by
          rcases mul_eq_zero.mp f1 with h | h
          · rw [h, zero_mul]
          · rw [h1 h, mul_zero]
        have g2 : w2 * a2 = 0 := by
          rcases mul_eq_zero.mp f2 with h | h
          · rw [h, zero_mul]
          · rw [h2 h, mul_zero]
        rw [hA, g1, g2] at hApos; linarith
      · exact hB0
    have hl : 0 < A / B := div_pos hApos hBpos
    have t1 := tangent w1 a1 b1 (A / B) hw1 ha1 hb1 h1 hl
    have t2 := tangent w2 a2 b2 (A / B) hw2 ha2 hb2 h2 hl
    have hAB : A / B * B = A := div_mul_cancel₀ A hBpos.ne'
    have : A * Real.log (A / B) = (w1 * a1 * Real.log (A / B) + w1 * a1 - A / B * (w1 * b1)) +
        (w2 * a2 * Real.log (A / B) + w2 * a2 - A / B * (w2 * b2)) := by
      have : A / B * (w1 * b1) + A / B * (w2 * b2) = A := by rw [← mul_add, ← hB, hAB]
      rw [hA] at this ⊢
      linarith
    rw [this]; linarith

lemma relEntropy_ne_bot {d : ℕ} (p q : Δ d) : relEntropy p q ≠ ⊥ := by
  unfold relEntropy; split_ifs
  · exact EReal.coe_ne_bot _
  · exact top_ne_bot

lemma mul_ne_bot' (c : ℝ) (hc : 0 < c) (x : EReal) (hx : x ≠ ⊥) : (c : EReal) * x ≠ ⊥ := by
  induction x using EReal.rec with
  | bot => exact absurd rfl hx
  | coe a => rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _
  | top => rw [EReal.coe_mul_top_of_pos hc]; exact top_ne_bot

end DROm4P1ii

open DROm4P1ii in
theorem solution {d : ℕ} (ℙ'₁ ℙ₁ ℙ'₂ ℙ₂ : Δ d) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    relEntropy (mix t ht ℙ'₁ ℙ'₂) (mix t ht ℙ₁ ℙ₂) ≤
      ((1 - t : ℝ) : EReal) * relEntropy ℙ'₁ ℙ₁ + ((t : ℝ) : EReal) * relEntropy ℙ'₂ ℙ₂ := by
  classical
  have hmix : ∀ (P Q : Δ d) i, ((mix t ht P Q : Δ d) : Fin d → ℝ) i =
      (1 - t) * (P : Fin d → ℝ) i + t * (Q : Fin d → ℝ) i := by
    intro P Q i; rfl
  rcases ht.1.eq_or_lt with h0 | h0
  · -- t = 0
    subst h0
    have e : ∀ P Q : Δ d, mix 0 ht P Q = P := by
      intro P Q; apply Subtype.ext; funext i; exact (hmix P Q i).trans (by ring_nf; rfl)
    rw [e, e]; simp
  rcases ht.2.eq_or_lt with h1 | h1
  · -- t = 1
    subst h1
    have e : ∀ P Q : Δ d, mix 1 ht P Q = Q := by
      intro P Q; apply Subtype.ext; funext i; exact (hmix P Q i).trans (by ring_nf; rfl)
    rw [e, e]; simp
  have hpos1 : (0 : ℝ) < 1 - t := by linarith
  by_cases hc1 : ∀ i, (ℙ₁ : Fin d → ℝ) i = 0 → (ℙ'₁ : Fin d → ℝ) i = 0
  · by_cases hc2 : ∀ i, (ℙ₂ : Fin d → ℝ) i = 0 → (ℙ'₂ : Fin d → ℝ) i = 0
    · have hcm : ∀ i, ((mix t ht ℙ₁ ℙ₂ : Δ d) : Fin d → ℝ) i = 0 →
          ((mix t ht ℙ'₁ ℙ'₂ : Δ d) : Fin d → ℝ) i = 0 := by
        intro i hi
        rw [hmix] at hi ⊢
        have n1 : 0 ≤ (ℙ₁ : Fin d → ℝ) i := ℙ₁.2.1 i
        have n2 : 0 ≤ (ℙ₂ : Fin d → ℝ) i := ℙ₂.2.1 i
        have f1 : (ℙ₁ : Fin d → ℝ) i = 0 := by nlinarith
        have f2 : (ℙ₂ : Fin d → ℝ) i = 0 := by nlinarith
        rw [hc1 i f1, hc2 i f2]; ring
      simp only [relEntropy, if_pos hc1, if_pos hc2, if_pos hcm]
      rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff,
        Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum (fun i _ => ?_)
      rw [hmix, hmix]
      exact logsum _ _ _ _ _ _ hpos1.le h0.le (ℙ'₁.2.1 i) (ℙ'₂.2.1 i) (ℙ₁.2.1 i) (ℙ₂.2.1 i)
        (hc1 i) (hc2 i)
    · have : relEntropy ℙ'₂ ℙ₂ = ⊤ := by simp only [relEntropy, if_neg hc2]
      rw [this, EReal.coe_mul_top_of_pos h0, EReal.add_top_of_ne_bot]
      · exact le_top
      · exact mul_ne_bot' _ hpos1 _ (relEntropy_ne_bot _ _)
  · have : relEntropy ℙ'₁ ℙ₁ = ⊤ := by simp only [relEntropy, if_neg hc1]
    rw [this, EReal.coe_mul_top_of_pos hpos1, EReal.top_add_of_ne_bot]
    · exact le_top
    · exact mul_ne_bot' _ h0 _ (relEntropy_ne_bot _ _)
