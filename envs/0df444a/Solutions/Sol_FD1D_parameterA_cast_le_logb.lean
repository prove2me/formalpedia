-- Prove2me | solution 1 for FD1D.parameterA_cast_le_logb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:22:24.984836+00:00
-- url     : https://prove2.me/submissions/f1ce6f22-13d0-4a46-8607-7c00478bb4f8

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters

set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics
namespace FD1D
theorem _root_.solution {m : ℕ} (hm : 2 ≤ m) :
    (parameterA m : ℝ) ≤ 800 * Real.logb 2 m := by
  have hlog_one :
      (1 : ℝ) ≤ Real.logb 2 (((m + 1 : ℕ) : ℝ)) := by
    calc
      (1 : ℝ) = Real.logb 2 2 :=
        (Real.logb_self_eq_one (by norm_num)).symm
      _ ≤ Real.logb 2 (((m + 1 : ℕ) : ℝ)) := by
        apply Real.logb_le_logb_of_le (by norm_num) (by norm_num)
        exact_mod_cast (show 2 ≤ m + 1 by omega)
  have hceil :
      (Nat.clog 2 (m + 1) : ℝ) ≤
        2 * Real.logb 2 (((m + 1 : ℕ) : ℝ)) := by
    rw [← Real.natCeil_logb_natCast]
    exact Nat.ceil_le_two_mul (by linarith)
  have hsq : m + 1 ≤ m ^ 2 := by
    nlinarith
  have hlog_sq :
      Real.logb 2 (((m + 1 : ℕ) : ℝ)) ≤
        2 * Real.logb 2 (m : ℝ) := by
    calc
      Real.logb 2 (((m + 1 : ℕ) : ℝ)) ≤
          Real.logb 2 ((m : ℝ) ^ 2) := by
        apply Real.logb_le_logb_of_le (by norm_num)
          (by positivity)
        exact_mod_cast hsq
      _ = 2 * Real.logb 2 m := by
        rw [Real.logb_pow]
        norm_num
  rw [parameterA, Nat.cast_mul]
  norm_num
  nlinarith
end FD1D
