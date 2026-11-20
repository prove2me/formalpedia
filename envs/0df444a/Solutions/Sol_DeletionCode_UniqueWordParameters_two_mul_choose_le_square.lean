-- Prove2me | solution 1 for DeletionCode.UniqueWordParameters.two_mul_choose_le_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:31.1003+00:00
-- url     : https://prove2.me/submissions/6f380cda-ead7-4ee6-829a-830a13664fb0

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
theorem _root_.solution (n : ℕ) : 2 * n.choose 2 ≤ n ^ 2 := by
  rw [Nat.choose_two_right]
  have hdiv := Nat.div_mul_le_self (n * (n - 1)) 2
  have hmul := Nat.mul_le_mul_left n (Nat.sub_le n 1)
  nlinarith
end DeletionCode.UniqueWordParameters
