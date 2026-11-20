-- Prove2me | solution 1 for DeletionCode.UniqueWordParameters.eight_mul_choose_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:57.133927+00:00
-- url     : https://prove2.me/submissions/e2c8270c-4972-44e7-a224-5d714f58e6f6

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_UniqueWordParameters
import Theorems.Thm_DeletionCode_UniqueWordParameters_two_mul_choose_le_square
import Theorems.Thm_DeletionCode_UniqueWordParameters_four_mul_square_le_pow

set_option autoImplicit true
open DeletionCode DeletionCode.UniqueWordParameters
namespace DeletionCode.UniqueWordParameters
theorem _root_.solution (n : ℕ) : 8 * n.choose 2 ≤ 2 ^ uniquenessLength n := by
  have hchoose := two_mul_choose_le_square n
  have hpow := four_mul_square_le_pow n
  omega
end DeletionCode.UniqueWordParameters
