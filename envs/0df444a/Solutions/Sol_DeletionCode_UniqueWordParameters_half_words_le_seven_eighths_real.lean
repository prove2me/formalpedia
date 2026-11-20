-- Prove2me | solution 1 for DeletionCode.UniqueWordParameters.half_words_le_seven_eighths_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:32.080331+00:00
-- url     : https://prove2.me/submissions/bf878824-8ff2-4b0d-9339-9ff56e8f5b9a

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
    (2 : ℝ) ^ (n - 1) ≤ (7 / 8 : ℝ) * (2 : ℝ) ^ n := by
  have hpow : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - 1) * 2 := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
  rw [hpow]
  have hnonneg := le_of_lt (pow_pos (by norm_num : (0 : ℝ) < 2) (n - 1))
  nlinarith
end DeletionCode.UniqueWordParameters
