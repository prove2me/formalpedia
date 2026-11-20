-- Prove2me | solution 1 for BirthdayEntropy.Soundness.Supplement.lemma_A_4
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T15:10:20.569937+00:00
-- url     : https://prove2.me/submissions/314441e7-0bec-436f-8324-977d971e02a3

import Mathlib
import Definitions.Def_bernoulliRelativeEntropy

open Real

/-- `y log (y / c) ≥ y - c` for `y ≥ 0`, `c > 0`. -/
lemma xlog_ge (y c : ℝ) (hy : 0 ≤ y) (hc : 0 < c) : y - c ≤ y * Real.log (y / c) := by
  rcases hy.eq_or_lt with rfl | hy
  · simp; linarith
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hy hc)
  rw [inv_div] at h
  have : y * (1 - c / y) = y - c := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left h hy.le]

theorem solution (lam x : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hx0 : 0 ≤ x) (hxlam : x ≤ lam / 4) :
    lam * (3/4 - Real.log 8 / 4) ≤
        BanditAlgorithm.bernoulliRelativeEntropy x lam - x * Real.log 2 ∧
      2 * lam / 9 < lam * (3/4 - Real.log 8 / 4) := by
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  refine ⟨?_, ?_⟩
  · set a := lam / 4 with ha
    have ha0 : 0 < a := by positivity
    have h1a : 0 < 1 - a := by linarith
    have h1l : 0 < 1 - lam := by linarith
    have h1x : 0 < 1 - x := by linarith
    set L := Real.log ((1 - a) / (1 - lam)) with hL
    -- the two tangent bounds
    have hA : (x - a) + x * Real.log (a / lam) ≤ x * Real.log (x / lam) := by
      rcases hx0.eq_or_lt with h0 | hxp
      · subst h0; simp; linarith
      have e : Real.log (x / lam) = Real.log (x / a) + Real.log (a / lam) := by
        rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
      rw [e, mul_add]; linarith [xlog_ge x a hx0 ha0]
    have hB : (a - x) + (1 - x) * L ≤ (1 - x) * Real.log ((1 - x) / (1 - lam)) := by
      have e : Real.log ((1 - x) / (1 - lam)) = Real.log ((1 - x) / (1 - a)) + L := by
        rw [hL, ← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
      rw [e, mul_add]
      have := xlog_ge (1 - x) (1 - a) h1x.le h1a
      linarith
    have hlogq : Real.log (a / lam) = -2 * Real.log 2 := by
      rw [ha, show lam / 4 / lam = (2 ^ 2 : ℝ)⁻¹ by field_simp; norm_num, Real.log_inv, Real.log_pow]
      norm_num
    -- (1 - a) L ≥ 3 lam / 4
    have hLb : 3 * lam / 4 ≤ (1 - a) * L := by
      have h := Real.one_sub_inv_le_log_of_pos (div_pos h1a h1l)
      rw [inv_div] at h
      have e : (1 - a) * (1 - (1 - lam) / (1 - a)) = 3 * lam / 4 := by
        rw [mul_sub, mul_one, mul_div_cancel₀ _ h1a.ne', ha]; ring
      nlinarith [mul_le_mul_of_nonneg_left h h1a.le]
    have hL0 : 0 ≤ L := by
      rw [hL]; exact Real.log_nonneg ((one_le_div h1l).mpr (by linarith))
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    unfold BanditAlgorithm.bernoulliRelativeEntropy
    rw [hlogq] at hA
    rw [hlog8]
    nlinarith [mul_nonneg (sub_nonneg.mpr hxlam) (add_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hlog2.le) hL0)]
  · rw [hlog8]
    have := Real.log_two_lt_d9
    nlinarith
