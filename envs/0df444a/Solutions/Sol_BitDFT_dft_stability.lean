-- Prove2me | solution 1 for BitDFT.dft_stability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T12:24:20.219359+00:00
-- url     : https://prove2.me/submissions/3238c779-1a48-47f3-82f8-1ae78d7eee43

import Definitions.Def_BitDFT_Numerics
import Theorems.Thm_BitDFT_guard_precision_bound
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open BitDFT

private lemma root_norm (n : ℕ) : ‖root n‖ = 1 := by
  rw [root, Complex.norm_exp]
  have h : (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ)).re = 0 := by
    simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
  rw [h, Real.exp_zero]

theorem solution {n : ℕ} (X Y : Fin n → ℂ) (δ : ℝ)
    (h : ∀ j, ‖X j - Y j‖ ≤ δ) (k : Fin n) :
    ‖dft X k - dft Y k‖ ≤ (n : ℝ) * δ := by
  simp only [dft, ← Finset.sum_sub_distrib, ← mul_sub]
  calc
    ‖∑ j : Fin n, root n ^ (-((j.val * k.val : ℕ) : ℤ)) * (X j - Y j)‖
      ≤ ∑ j : Fin n, ‖root n ^ (-((j.val * k.val : ℕ) : ℤ)) * (X j - Y j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, δ := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [norm_mul, norm_zpow, root_norm, one_zpow, one_mul] using h j
    _ = (n : ℝ) * δ := by simp

