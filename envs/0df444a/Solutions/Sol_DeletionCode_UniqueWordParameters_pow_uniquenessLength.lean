-- Prove2me | solution 1 for DeletionCode.UniqueWordParameters.pow_uniquenessLength
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:31.579021+00:00
-- url     : https://prove2.me/submissions/044bbf65-a46d-44ad-94e4-88e12a71bfbf

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
theorem _root_.solution (n : ℕ) :
    2 ^ uniquenessLength n = 4 * (2 ^ Nat.clog 2 n) ^ 2 := by
  unfold uniquenessLength
  rw [show 2 * Nat.clog 2 n = Nat.clog 2 n * 2 by omega, pow_add, pow_mul]
  ring
end DeletionCode.UniqueWordParameters
