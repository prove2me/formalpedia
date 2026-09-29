-- Prove2me | solution 1 for Freiman.cfValue_finite_prefix
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:21:39.230179+00:00
-- url     : https://prove2.me/submissions/0dca8541-9740-4a81-b34c-c9a1c58a8c02

import Theorems.Thm_Freiman_cfValue_prefix
import Theorems.Thm_Freiman_prefixEval_cylinder_bound
import Theorems.Thm_Freiman_prefixEval_zero
import Theorems.Thm_Freiman_cf_convergence

open Freiman
set_option autoImplicit false

theorem solution (b : ℕ → ℕ+) (m : ℕ) :
    |cfValue b - cfConvergent b m| ≤ 1 / ((Nat.fib (m + 1) : ℝ) ^ 2) := by
  have hb := cf_convergence (fun k => b (m + k))
  rw [cfValue_prefix b m]
  unfold cfConvergent
  rw [← prefixEval_zero]
  simpa only [List.length_map, List.length_range] using
    prefixEval_cylinder_bound ((List.range m).map b)
      (cfValue (fun k => b (m + k))) 0
      ⟨hb.2.2.1.le, hb.2.2.2.1.le⟩ ⟨le_rfl, by norm_num⟩
