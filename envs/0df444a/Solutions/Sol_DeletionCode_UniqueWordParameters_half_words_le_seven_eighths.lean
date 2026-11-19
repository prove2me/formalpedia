-- Prove2me | solution 1 for DeletionCode.UniqueWordParameters.half_words_le_seven_eighths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:41:57.101988+00:00
-- url     : https://prove2.me/submissions/eeaad86f-c80c-4167-8a67-0368d9f349e2

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_UniqueWordParameters

set_option autoImplicit true
open DeletionCode DeletionCode.UniqueWordParameters
namespace DeletionCode.UniqueWordParameters
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℚ) ^ (n - 1) ≤ (7 / 8 : ℚ) * (2 : ℚ) ^ n := by
  have hpow : (2 : ℚ) ^ n = (2 : ℚ) ^ (n - 1) * 2 := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
  rw [hpow]
  have hnonneg := le_of_lt (pow_pos (by norm_num : (0 : ℚ) < 2) (n - 1))
  nlinarith
end DeletionCode.UniqueWordParameters
