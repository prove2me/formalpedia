-- Prove2me | solution 1 for DeletionCode.UniqueWordParameters.count_lower_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:21:26.239182+00:00
-- url     : https://prove2.me/submissions/b00cfe48-2dc8-461f-a514-57d7e3e0ae83

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_UniqueWordParameters
import Theorems.Thm_DeletionCode_UniqueWordParameters_seven_eighths_le_retained
import Theorems.Thm_DeletionCode_UniqueWordParameters_half_words_le_seven_eighths

set_option autoImplicit true
open DeletionCode DeletionCode.UniqueWordParameters
namespace DeletionCode.UniqueWordParameters
theorem _root_.solution (n count : ℕ) (hn : 1 ≤ n)
    (hcount : (1 - (n.choose 2 : ℚ) / (2 : ℚ) ^ uniquenessLength n) * (2 : ℚ) ^ n ≤ count) :
    (7 / 8 : ℚ) * (2 : ℚ) ^ n ≤ count ∧ 2 ^ (n - 1) ≤ count := by
  have hlarge := (seven_eighths_le_retained n).trans hcount
  refine ⟨hlarge, ?_⟩
  exact_mod_cast (half_words_le_seven_eighths n hn).trans hlarge
end DeletionCode.UniqueWordParameters
