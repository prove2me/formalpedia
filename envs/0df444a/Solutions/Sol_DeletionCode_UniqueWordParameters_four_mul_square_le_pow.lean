-- Prove2me | solution 1 for DeletionCode.UniqueWordParameters.four_mul_square_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:47.23498+00:00
-- url     : https://prove2.me/submissions/88de2198-5062-4f5e-8bfc-829ebc39dbeb

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_UniqueWordParameters
import Theorems.Thm_DeletionCode_UniqueWordParameters_pow_uniquenessLength

set_option autoImplicit true
open DeletionCode DeletionCode.UniqueWordParameters
namespace DeletionCode.UniqueWordParameters
theorem _root_.solution (n : ℕ) : 4 * n ^ 2 ≤ 2 ^ uniquenessLength n := by
  have hn := Nat.le_pow_clog (by decide : 1 < 2) n
  have hsquare := Nat.mul_le_mul hn hn
  rw [pow_uniquenessLength]
  nlinarith
end DeletionCode.UniqueWordParameters
