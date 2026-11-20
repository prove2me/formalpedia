-- Prove2me | solution 1 for DeletionCode.RedundancyBounds.redundancy_le_log_labels
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:17.212172+00:00
-- url     : https://prove2.me/submissions/bf78655b-77d0-48e8-a5a7-6ef8bf594a1b

import Definitions.Def_DeletionCode_PaperParameters
import Definitions.Def_DeletionCode_WitnessCost
import Definitions.Def_DeletionCode_RedundancyBounds
import Theorems.Thm_DeletionCode_RedundancyBounds_card_positive
import Theorems.Thm_DeletionCode_RedundancyBounds_logb_eight

set_option autoImplicit true
open DeletionCode DeletionCode.RedundancyBounds
open HeaderRecovery
namespace DeletionCode.RedundancyBounds
theorem _root_.solution (n Q : ℕ) (C : Finset (Bits n))
    (hQ : 1 ≤ Q) (hcard : 2 ^ n ≤ 8 * Q * C.card) :
    redundancy n C ≤ Real.logb 2 (Q : ℝ) + 3 := by
  have hc : (0 : ℝ) < C.card := by exact_mod_cast card_positive n Q C hcard
  have hq : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hreal : (2 : ℝ) ^ n ≤ 8 * (Q : ℝ) * (C.card : ℝ) := by exact_mod_cast hcard
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (pow_pos (by norm_num : (0 : ℝ) < 2) n) hreal
  rw [Real.logb_mul (mul_ne_zero (by norm_num : (8 : ℝ) ≠ 0) (ne_of_gt hq)) (ne_of_gt hc),
    Real.logb_mul (by norm_num : (8 : ℝ) ≠ 0) (ne_of_gt hq)] at hlog
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
    mul_one, logb_eight] at hlog
  unfold redundancy
  linarith
end DeletionCode.RedundancyBounds
