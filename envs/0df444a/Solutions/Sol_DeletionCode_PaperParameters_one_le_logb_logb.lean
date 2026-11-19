-- Prove2me | solution 1 for DeletionCode.PaperParameters.one_le_logb_logb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:47:39.73226+00:00
-- url     : https://prove2.me/submissions/327870be-c61e-4607-93c3-90fd48e275a7

import Definitions.Def_DeletionCode_UniqueWordParameters
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Analysis.Asymptotics.Defs
import Definitions.Def_DeletionCode_PaperParameters
import Theorems.Thm_DeletionCode_PaperParameters_two_le_logb

set_option autoImplicit true
open DeletionCode DeletionCode.PaperParameters
open Filter Asymptotics
open scoped Topology
namespace DeletionCode.PaperParameters
theorem _root_.solution (n : ℕ) (hn : 4 ≤ n) :
    1 ≤ Real.logb 2 (Real.logb 2 (n : ℝ)) := by
  have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2) (two_le_logb n hn)
  simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using h
end DeletionCode.PaperParameters
