-- Prove2me | solution 1 for BayesBAI.lemma_11
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T08:07:39.308354+00:00
-- url     : https://prove2.me/submissions/3fd0d71a-acfe-41e2-929b-c63083e856f5

import Mathlib
import Definitions.Def_BayesBAI_KLSetting
import Definitions.Def_RegretBandits_Stochastic_klBernoulli

open BayesBAI RegretBandits.Stochastic Finset

lemma cubic (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    |Real.log (1 + x) - x + x ^ 2 / 2| ≤ 2 * x ^ 3 ∧ |Real.log (1 - x) + x + x ^ 2 / 2| ≤ 2 * x ^ 3 := by
  have hx : |x| = x := abs_of_nonneg h0
  have hb : x ^ 3 / (1 - x) ≤ 2 * x ^ 3 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [pow_nonneg h0 3]
  constructor
  · have := Real.abs_log_sub_add_sum_range_le (x := -x) (by rw [abs_neg, hx]; linarith) 2
    simp only [sum_range_succ, sum_range_zero, abs_neg, hx, sub_neg_eq_add] at this
    refine le_trans (le_of_eq ?_) (this.trans hb); congr 1; push_cast; ring
  · have := Real.abs_log_sub_add_sum_range_le (x := x) (by rw [hx]; linarith) 2
    simp only [sum_range_succ, sum_range_zero, hx] at this
    refine le_trans (le_of_eq ?_) (this.trans hb); congr 1; push_cast; ring

theorem solution {T l u h : ℝ} (hs : KLSetting T l u h) :
    |klBern l u - (u - l) ^ 2 / (2 * l * (1 - l))| ≤ 8 * h ^ 3 * T ^ ((1 : ℝ) / 3) := by
  obtain ⟨hT, _, hh, hl1, hl2, hlu, hu⟩ := hs
  set ε := T ^ (-(1 / 6) : ℝ) with hε
  have hε0 : 0 < ε := Real.rpow_pos_of_pos hT _
  have hε2 : T ^ ((1 : ℝ) / 3) = 1 / ε ^ 2 := by
    rw [hε, ← Real.rpow_natCast, ← Real.rpow_mul hT.le, one_div (_ ^ _), ← Real.rpow_neg hT.le]
    norm_num
  set δ := u - l with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hδh : δ < h := by rw [hδ]; linarith
  have hhpos : 0 < h := by linarith
  have hl0 : 0 < l := lt_of_lt_of_le hε0 hl1
  have hl1' : ε ≤ 1 - l := by linarith
  have h1l : 0 < 1 - l := lt_of_lt_of_le hε0 hl1'
  set a := δ / l with ha
  set b := δ / (1 - l) with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have ha1 : a ≤ 1 / 2 := by
    rw [ha, div_le_iff₀ hl0]; nlinarith
  have hb1 : b ≤ 1 / 2 := by
    rw [hb, div_le_iff₀ h1l]; nlinarith
  obtain ⟨hE1, _⟩ := cubic a ha0 ha1
  obtain ⟨_, hE2⟩ := cubic b hb0 hb1
  have hu0 : 0 < u := by linarith
  have h1u : 0 < 1 - u := by
    have : b < 1 := by linarith
    rw [hb, div_lt_one h1l] at this; linarith
  have hlog1 : Real.log (l / u) = -Real.log (1 + a) := by
    rw [← Real.log_inv]; congr 1; rw [ha, hδ, show 1 + (u - l) / l = u / l by field_simp [hl0.ne']; ring, inv_div]
  have hlog2 : Real.log ((1 - l) / (1 - u)) = -Real.log (1 - b) := by
    rw [← Real.log_inv]; congr 1; rw [hb, hδ, show 1 - (u - l) / (1 - l) = (1 - u) / (1 - l) by field_simp [h1l.ne']; ring, inv_div]
  have hkey : klBern l u - δ ^ 2 / (2 * l * (1 - l)) =
      -l * (Real.log (1 + a) - a + a ^ 2 / 2) - (1 - l) * (Real.log (1 - b) + b + b ^ 2 / 2) := by
    unfold klBern; rw [hlog1, hlog2, ha, hb]; field_simp; ring
  rw [hkey]
  have hfin : l * (2 * a ^ 3) + (1 - l) * (2 * b ^ 3) ≤ 8 * h ^ 3 * T ^ ((1 : ℝ) / 3) := by
    have e1 : l * (2 * a ^ 3) = 2 * δ ^ 3 / l ^ 2 := by rw [ha]; field_simp
    have e2 : (1 - l) * (2 * b ^ 3) = 2 * δ ^ 3 / (1 - l) ^ 2 := by rw [hb]; field_simp
    have hδ3 : δ ^ 3 ≤ h ^ 3 := pow_le_pow_left₀ hδ0.le hδh.le 3
    have f1 : 2 * δ ^ 3 / l ^ 2 ≤ 2 * h ^ 3 / ε ^ 2 :=
      div_le_div₀ (by positivity) (by linarith) (by positivity) (pow_le_pow_left₀ hε0.le hl1 2)
    have f2 : 2 * δ ^ 3 / (1 - l) ^ 2 ≤ 2 * h ^ 3 / ε ^ 2 :=
      div_le_div₀ (by positivity) (by linarith) (by positivity) (pow_le_pow_left₀ hε0.le hl1' 2)
    rw [e1, e2, hε2]
    have hh0 : 0 ≤ h ^ 3 / ε ^ 2 := by have : 0 < h := by linarith
                                       positivity
    calc 2 * δ ^ 3 / l ^ 2 + 2 * δ ^ 3 / (1 - l) ^ 2 ≤ 2 * h ^ 3 / ε ^ 2 + 2 * h ^ 3 / ε ^ 2 := add_le_add f1 f2
      _ ≤ 8 * h ^ 3 * (1 / ε ^ 2) := by
        have : 2 * h ^ 3 / ε ^ 2 = 2 * (h ^ 3 / ε ^ 2) := by ring
        have : 8 * h ^ 3 * (1 / ε ^ 2) = 8 * (h ^ 3 / ε ^ 2) := by ring
        linarith
  calc |-l * (Real.log (1 + a) - a + a ^ 2 / 2) - (1 - l) * (Real.log (1 - b) + b + b ^ 2 / 2)|
      ≤ |-l * (Real.log (1 + a) - a + a ^ 2 / 2)| + |(1 - l) * (Real.log (1 - b) + b + b ^ 2 / 2)| :=
        abs_sub _ _
    _ = l * |Real.log (1 + a) - a + a ^ 2 / 2| + (1 - l) * |Real.log (1 - b) + b + b ^ 2 / 2| := by
        rw [abs_mul, abs_mul, abs_neg, abs_of_pos hl0, abs_of_pos h1l]
    _ ≤ l * (2 * a ^ 3) + (1 - l) * (2 * b ^ 3) := by gcongr
    _ ≤ _ := hfin
