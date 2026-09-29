-- Prove2me | solution 1 for Freiman.perronValue_gt_digit
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:27:17.436382+00:00
-- url     : https://prove2.me/submissions/17106cfe-1fec-4187-af34-9fe6b5729aad

import Definitions.Def_Freiman_perronArithmetic
import Theorems.Thm_Freiman_prefixEval_mem_Icc
import Theorems.Thm_Freiman_prefixEval_zero
import Theorems.Thm_Freiman_cf_convergence

open Freiman

theorem solution (b : ℕ → ℕ+) (n : ℕ) :
    ((b n:ℕ):ℝ) < perronValue b n := by
  have hb := (prefixEval_mem_Icc (((List.range n).map b).reverse) 0 (by constructor <;> norm_num)).1
  rw [prefixEval_zero] at hb
  have ht := (cf_convergence (fun k => b (n+1+k))).2.2.1
  unfold perronValue
  linarith
