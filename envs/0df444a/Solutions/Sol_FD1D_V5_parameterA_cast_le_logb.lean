-- Prove2me | solution 1 for FD1D.V5.parameterA_cast_le_logb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:20:15.709154+00:00
-- url     : https://prove2.me/submissions/6ced973f-538c-49e6-9f11-e84f3e697f0e

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_V5_Parameters

set_option autoImplicit true
open FD1D FD1D.V5
noncomputable section
open Filter Asymptotics
namespace FD1D.V5
theorem _root_.solution {m : ℕ} (hm : 2 ≤ m) :
    (parameterA m : ℝ) ≤ 8000 * Real.logb 2 m := by
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
  have hsq : m + 1 ≤ m ^ 2 := by nlinarith
  have hlog_sq :
      Real.logb 2 (((m + 1 : ℕ) : ℝ)) ≤
        2 * Real.logb 2 (m : ℝ) := by
    calc
      Real.logb 2 (((m + 1 : ℕ) : ℝ)) ≤
          Real.logb 2 ((m : ℝ) ^ 2) := by
        apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
        exact_mod_cast hsq
      _ = 2 * Real.logb 2 m := by
        rw [Real.logb_pow]
        norm_num
  rw [parameterA, Nat.cast_mul]
  norm_num
  nlinarith
end FD1D.V5
