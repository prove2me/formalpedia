-- Prove2me | solution 1 for DeletionCode.PaperParameters.logb_L_isBigO_logb_logb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:26.411812+00:00
-- url     : https://prove2.me/submissions/d7ef8925-3b75-41ee-b3f0-0558f1988235

import Definitions.Def_DeletionCode_UniqueWordParameters
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Analysis.Asymptotics.Defs
import Definitions.Def_DeletionCode_PaperParameters
import Theorems.Thm_DeletionCode_PaperParameters_nine_le_L
import Theorems.Thm_DeletionCode_PaperParameters_one_le_logb_logb
import Theorems.Thm_DeletionCode_PaperParameters_logb_L_le_six_logb_logb

set_option autoImplicit true
open DeletionCode DeletionCode.PaperParameters
open Filter Asymptotics
open scoped Topology
namespace DeletionCode.PaperParameters
theorem _root_.solution :
    (fun n : ℕ => Real.logb 2 (L n : ℝ)) =O[atTop]
      (fun n => Real.logb 2 (Real.logb 2 (n : ℝ))) := by
  apply Asymptotics.IsBigO.of_bound 6
  filter_upwards [eventually_ge_atTop 4] with n hn
  have hL : 0 ≤ Real.logb 2 (L n : ℝ) := Real.logb_nonneg
    (by norm_num : (1 : ℝ) < 2) (by exact_mod_cast (show 1 ≤ L n by have := nine_le_L n; omega))
  have hll : 0 ≤ Real.logb 2 (Real.logb 2 (n : ℝ)) := by
    have := one_le_logb_logb n hn
    linarith
  simpa only [Real.norm_eq_abs, abs_of_nonneg hL, abs_of_nonneg hll] using
    logb_L_le_six_logb_logb n hn
end DeletionCode.PaperParameters
