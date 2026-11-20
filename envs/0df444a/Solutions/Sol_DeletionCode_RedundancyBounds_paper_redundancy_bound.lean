-- Prove2me | solution 1 for DeletionCode.RedundancyBounds.paper_redundancy_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:24.343654+00:00
-- url     : https://prove2.me/submissions/6aaa2f0b-d330-4420-8c05-2b77df4e50c5

import Definitions.Def_DeletionCode_PaperParameters
import Definitions.Def_DeletionCode_WitnessCost
import Definitions.Def_DeletionCode_RedundancyBounds
import Theorems.Thm_DeletionCode_RedundancyBounds_redundancy_le_log_labels
import Theorems.Thm_DeletionCode_RedundancyBounds_labelCount_positive
import Theorems.Thm_DeletionCode_RedundancyBounds_logb_labelCount
import Theorems.Thm_DeletionCode_PaperParameters_logb_L_le_six_logb_logb
import Theorems.Thm_DeletionCode_PaperParameters_one_le_logb_logb


set_option autoImplicit true
open DeletionCode DeletionCode.RedundancyBounds
open HeaderRecovery
namespace DeletionCode.RedundancyBounds
theorem _root_.solution (t n : ℕ) (C : Finset (Bits n)) (hn : 4 ≤ n)
    (hcard : 2 ^ n ≤ 8 * labelCount t n * C.card) :
    redundancy n C ≤
      ((2 * t - 1 : ℕ) : ℝ) * Real.logb 2 (n : ℝ) +
        ((6 * WitnessCost.exponent t + 6 : ℕ) : ℝ) *
          Real.logb 2 (Real.logb 2 (n : ℝ)) := by
  have hn' : 1 ≤ n := by omega
  have hbase := redundancy_le_log_labels n (labelCount t n) C
    (labelCount_positive t n hn') hcard
  rw [logb_labelCount t n hn'] at hbase
  have hwindow := mul_le_mul_of_nonneg_left
    (PaperParameters.logb_L_le_six_logb_logb n hn)
    (Nat.cast_nonneg (WitnessCost.exponent t) : (0 : ℝ) ≤ (WitnessCost.exponent t : ℝ))
  have hloglog := PaperParameters.one_le_logb_logb n hn
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  nlinarith
end DeletionCode.RedundancyBounds
