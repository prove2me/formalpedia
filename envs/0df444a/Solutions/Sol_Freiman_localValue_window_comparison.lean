-- Prove2me | solution 1 for Freiman.localValue_window_comparison
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:21:14.170918+00:00
-- url     : https://prove2.me/submissions/44ea8c18-cf21-4814-b1f0-3ddaf82ccd61

import Definitions.Def_Freiman_paddedCopies
import Mathlib.Data.Nat.Fib.Basic
import Theorems.Thm_Freiman_localValue_window_bound
import Theorems.Thm_Freiman_localValue_shift
import Mathlib.Tactic.Linarith

open Freiman
set_option autoImplicit false

theorem solution (a b : ℤ → ℕ+) (i j : ℤ) (R : ℕ)
    (h : ∀ k : ℤ, -(R : ℤ) ≤ k → k ≤ (R : ℤ) → a (i + k) = b (j + k)) :
    |localValue a i - localValue b j| ≤ 2 / ((Nat.fib (R + 1) : ℝ) ^ 2) := by
  have hw := localValue_window_bound (fun k : ℤ => a (i + k))
    (fun k : ℤ => b (j + k)) 0 R (by
      intro k hk₁ hk₂
      exact h k (by simpa using hk₁) (by simpa using hk₂))
  simpa only [localValue_shift, add_zero] using hw
