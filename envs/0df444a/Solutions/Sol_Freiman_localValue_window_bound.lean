-- Prove2me | solution 1 for Freiman.localValue_window_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:21:39.259399+00:00
-- url     : https://prove2.me/submissions/ceb9ad3f-c604-42f2-b09d-78bac9dd3e1b

import Definitions.Def_Freiman_symbolicMarkovSpectrum
import Theorems.Thm_Freiman_cfValue_cylinder_bound
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Ring.Abs

open Freiman

theorem solution (a b : ℤ → ℕ+) (i : ℤ) (R : ℕ)
    (h : ∀ j : ℤ, i - (R : ℤ) ≤ j → j ≤ i + (R : ℤ) → a j = b j) :
    |localValue a i - localValue b i| ≤ 2 / ((Nat.fib (R + 1) : ℝ) ^ 2) := by
  have hcenter : a i = b i := h i (by omega) (by omega)
  have hleft := cfValue_cylinder_bound
    (fun k : ℕ => a (i - (k : ℤ) - 1))
    (fun k : ℕ => b (i - (k : ℤ) - 1)) R (by
      intro k hk
      exact h _ (by omega) (by omega))
  have hright := cfValue_cylinder_bound
    (fun k : ℕ => a (i + (k : ℤ) + 1))
    (fun k : ℕ => b (i + (k : ℤ) + 1)) R (by
      intro k hk
      exact h _ (by omega) (by omega))
  have hsplit : localValue a i - localValue b i =
      (cfValue (fun k : ℕ => a (i - (k : ℤ) - 1)) -
        cfValue (fun k : ℕ => b (i - (k : ℤ) - 1))) +
      (cfValue (fun k : ℕ => a (i + (k : ℤ) + 1)) -
        cfValue (fun k : ℕ => b (i + (k : ℤ) + 1))) := by
    unfold localValue
    rw [hcenter]
    ring
  rw [hsplit]
  exact (abs_add_le _ _).trans ((add_le_add hleft hright).trans_eq (by ring))
