-- Prove2me | solution 1 for Freiman.cfValue_cylinder_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:21:25.855299+00:00
-- url     : https://prove2.me/submissions/6ae920aa-9c96-45b0-a2cc-0b6a68551bfb

import Theorems.Thm_Freiman_cfValue_prefix
import Theorems.Thm_Freiman_prefixEval_cylinder_bound
import Theorems.Thm_Freiman_cf_convergence

open Freiman
set_option autoImplicit false

theorem solution (b c : ℕ → ℕ+) (m : ℕ) (h : ∀ k : ℕ, k < m → b k = c k) :
    |cfValue b - cfValue c| ≤ 1 / ((Nat.fib (m + 1) : ℝ) ^ 2) := by
  have hword : (List.range m).map b = (List.range m).map c := by
    apply List.map_congr_left
    intro k hk
    exact h k (List.mem_range.mp hk)
  have hb := cf_convergence (fun k => b (m + k))
  have hc := cf_convergence (fun k => c (m + k))
  rw [cfValue_prefix b m, cfValue_prefix c m, ← hword]
  simpa only [List.length_map, List.length_range] using
    prefixEval_cylinder_bound ((List.range m).map b)
      (cfValue (fun k => b (m + k))) (cfValue (fun k => c (m + k)))
      ⟨hb.2.2.1.le, hb.2.2.2.1.le⟩ ⟨hc.2.2.1.le, hc.2.2.2.1.le⟩
