-- Prove2me | solution 1 for DeletionCode.PaperParameters.logb_L_le_six_logb_logb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:48:25.623171+00:00
-- url     : https://prove2.me/submissions/22db0743-92f3-4190-ae10-056acbc83171

import Definitions.Def_DeletionCode_UniqueWordParameters
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Analysis.Asymptotics.Defs
import Definitions.Def_DeletionCode_PaperParameters
import Theorems.Thm_DeletionCode_PaperParameters_nine_le_L
import Theorems.Thm_DeletionCode_PaperParameters_two_le_logb
import Theorems.Thm_DeletionCode_PaperParameters_L_le_twenty_one_logb
import Theorems.Thm_DeletionCode_PaperParameters_one_le_logb_logb

set_option autoImplicit true
open DeletionCode DeletionCode.PaperParameters
open Filter Asymptotics
open scoped Topology
namespace DeletionCode.PaperParameters
theorem _root_.solution (n : ℕ) (hn : 4 ≤ n) :
    Real.logb 2 (L n : ℝ) ≤ 6 * Real.logb 2 (Real.logb 2 (n : ℝ)) := by
  have hlog : 0 < Real.logb 2 (n : ℝ) := by have := two_le_logb n hn; linarith
  have hL : (0 : ℝ) < L n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 9) (nine_le_L n))
  have hmono := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    hL (L_le_twenty_one_logb n (by omega))
  rw [Real.logb_mul (by norm_num : (21 : ℝ) ≠ 0) (ne_of_gt hlog)] at hmono
  have h21 : Real.logb 2 (21 : ℝ) ≤ 5 := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 21) (by norm_num : (21 : ℝ) ≤ 2 ^ (5 : ℕ))
    simpa only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
      Nat.cast_ofNat, mul_one] using h
  have hll := one_le_logb_logb n hn
  linarith
end DeletionCode.PaperParameters
