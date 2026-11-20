-- Prove2me | solution 1 for DeletionCode.UniqueWordParameters.seven_eighths_le_retained_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:20:49.461457+00:00
-- url     : https://prove2.me/submissions/18a3f310-adc5-46c3-87d1-a39101ae8042

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_UniqueWordParameters
import Theorems.Thm_DeletionCode_UniqueWordParameters_collision_fraction_le_real

set_option autoImplicit true
open DeletionCode DeletionCode.UniqueWordParameters
namespace DeletionCode.UniqueWordParameters
theorem _root_.solution (n : ℕ) :
    (7 / 8 : ℝ) * (2 : ℝ) ^ n ≤
      (1 - (n.choose 2 : ℝ) / (2 : ℝ) ^ uniquenessLength n) * (2 : ℝ) ^ n := by
  apply mul_le_mul_of_nonneg_right
  · have h := collision_fraction_le_real n
    linarith
  · exact le_of_lt (pow_pos (by norm_num : (0 : ℝ) < 2) n)
end DeletionCode.UniqueWordParameters
