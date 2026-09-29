-- Prove2me | solution 1 for Freiman.prefixEval_cylinder_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:21:25.903915+00:00
-- url     : https://prove2.me/submissions/d3e5592c-a850-48ae-94d9-d87ba2e7c26b

import Theorems.Thm_Freiman_prefixEval_difference
import Theorems.Thm_Freiman_continuant_fibonacci
import Theorems.Thm_Freiman_continuant_denominator_pos

open Freiman
set_option autoImplicit false

theorem solution (w : List ℕ+) (x y : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |prefixEval w x - prefixEval w y| ≤ 1 / ((Nat.fib (w.length + 1) : ℝ) ^ 2) := by
  rw [prefixEval_difference w x y hx hy]
  have hF : 0 < (Nat.fib (w.length + 1) : ℝ) := by
    exact_mod_cast (Nat.fib_pos.mpr (Nat.succ_pos w.length))
  have hQ : 0 < (wordContinuantQ w : ℝ) := by
    exact_mod_cast continuant_denominator_pos w
  have hFQ : (Nat.fib (w.length + 1) : ℝ) ≤ wordContinuantQ w := by
    exact_mod_cast continuant_fibonacci w
  have hprev : 0 ≤ (wordContinuantPrevQ w : ℝ) := Nat.cast_nonneg _
  have hden : (Nat.fib (w.length + 1) : ℝ) ^ 2 ≤
      ((wordContinuantQ w : ℝ) + x * wordContinuantPrevQ w) *
        ((wordContinuantQ w : ℝ) + y * wordContinuantPrevQ w) := by
    have h₁ : (Nat.fib (w.length + 1) : ℝ) ≤
        (wordContinuantQ w : ℝ) + x * wordContinuantPrevQ w :=
      hFQ.trans (le_add_of_nonneg_right (mul_nonneg hx.1 hprev))
    have h₂ : (Nat.fib (w.length + 1) : ℝ) ≤
        (wordContinuantQ w : ℝ) + y * wordContinuantPrevQ w :=
      hFQ.trans (le_add_of_nonneg_right (mul_nonneg hy.1 hprev))
    simpa only [pow_two] using mul_le_mul h₁ h₂ hF.le (hF.le.trans h₁)
  have hD : 0 < ((wordContinuantQ w : ℝ) + x * wordContinuantPrevQ w) *
      ((wordContinuantQ w : ℝ) + y * wordContinuantPrevQ w) :=
    lt_of_lt_of_le (sq_pos_of_pos hF) hden
  have hxy : |x - y| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩
  exact (div_le_div_of_nonneg_right hxy hD.le).trans
    (div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hF) hden)
