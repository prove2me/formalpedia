-- Prove2me | solution 1 for DeletionCode.PaperParameters.L_isBigO_logb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:15.796238+00:00
-- url     : https://prove2.me/submissions/ecfd2416-98f9-45f3-81ac-ffa8db602112

import Definitions.Def_DeletionCode_UniqueWordParameters
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Analysis.Asymptotics.Defs
import Definitions.Def_DeletionCode_PaperParameters
import Theorems.Thm_DeletionCode_PaperParameters_one_le_logb
import Theorems.Thm_DeletionCode_PaperParameters_L_le_twenty_one_logb

set_option autoImplicit true
open DeletionCode DeletionCode.PaperParameters
open Filter Asymptotics
open scoped Topology
namespace DeletionCode.PaperParameters
theorem _root_.solution :
    (fun n : ℕ => (L n : ℝ)) =O[atTop] (fun n => Real.logb 2 (n : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 21
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlog : 0 ≤ Real.logb 2 (n : ℝ) := by have := one_le_logb n hn; linarith
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg (L n) : (0 : ℝ) ≤ (L n : ℝ)),
    abs_of_nonneg hlog] using L_le_twenty_one_logb n hn
end DeletionCode.PaperParameters
