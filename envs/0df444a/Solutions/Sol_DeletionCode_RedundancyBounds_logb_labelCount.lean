-- Prove2me | solution 1 for DeletionCode.RedundancyBounds.logb_labelCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:18.29341+00:00
-- url     : https://prove2.me/submissions/73885931-ede9-4775-a72c-e511e1c4890b

import Definitions.Def_DeletionCode_PaperParameters
import Definitions.Def_DeletionCode_WitnessCost
import Definitions.Def_DeletionCode_RedundancyBounds
import Theorems.Thm_DeletionCode_RedundancyBounds_logb_eight
import Theorems.Thm_DeletionCode_PaperParameters_nine_le_L


set_option autoImplicit true
open DeletionCode DeletionCode.RedundancyBounds
open HeaderRecovery
namespace DeletionCode.RedundancyBounds
theorem _root_.solution (t n : ℕ) (hn : 1 ≤ n) :
    Real.logb 2 (labelCount t n : ℝ) =
      3 + ((2 * t - 1 : ℕ) : ℝ) * Real.logb 2 (n : ℝ) +
        (WitnessCost.exponent t : ℝ) * Real.logb 2 (PaperParameters.L n : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hLpos : (0 : ℝ) < PaperParameters.L n := by
    exact_mod_cast (show 0 < PaperParameters.L n by have := PaperParameters.nine_le_L n; omega)
  have hnzero : (n : ℝ) ^ (2 * t - 1) ≠ 0 := pow_ne_zero _ (ne_of_gt hnpos)
  have hLzero : (PaperParameters.L n : ℝ) ^ (WitnessCost.exponent t) ≠ 0 :=
    pow_ne_zero _ (ne_of_gt hLpos)
  simp only [labelCount, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  rw [Real.logb_mul (mul_ne_zero (by norm_num : (8 : ℝ) ≠ 0) hnzero) hLzero,
    Real.logb_mul (by norm_num : (8 : ℝ) ≠ 0) hnzero,
    logb_eight, Real.logb_pow, Real.logb_pow]
end DeletionCode.RedundancyBounds
