-- Prove2me | solution 1 for Freiman.perron_local_difference_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:21:39.168841+00:00
-- url     : https://prove2.me/submissions/4ee98c24-31d0-4816-9c11-e7b1d36bb3bd

import Theorems.Thm_Freiman_perron_backward_prefix
import Theorems.Thm_Freiman_cfValue_finite_prefix
import Definitions.Def_Freiman_symbolicMarkovSpectrum
import Mathlib.Tactic.Ring

open Freiman
set_option autoImplicit false

theorem solution (a : ℤ → ℕ+) (n : ℕ) :
    |perronValue (fun k : ℕ => a (k : ℤ)) n - localValue a (n : ℤ)| ≤
      1 / ((Nat.fib (n + 1) : ℝ) ^ 2) := by
  have hb := cfValue_finite_prefix (fun k : ℕ => a ((n : ℤ) - (k : ℤ) - 1)) n
  rw [abs_sub_comm] at hb
  have hright : (fun k : ℕ => a ((n + 1 + k : ℕ) : ℤ)) =
      (fun k : ℕ => a ((n : ℤ) + (k : ℤ) + 1)) := by
    funext k
    congr 1
    push_cast
    ring
  have heq : perronValue (fun k : ℕ => a (k : ℤ)) n - localValue a (n : ℤ) =
      cfConvergent (fun k : ℕ => a ((n : ℤ) - (k : ℤ) - 1)) n -
      cfValue (fun k : ℕ => a ((n : ℤ) - (k : ℤ) - 1)) := by
    unfold perronValue localValue
    rw [perron_backward_prefix, hright]
    ring
  rw [heq]
  exact hb
