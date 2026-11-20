-- Prove2me | solution 1 for DeletionCode.ExceptionalCountArithmetic.exceptionalConstant_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:55.733882+00:00
-- url     : https://prove2.me/submissions/58628989-2cfe-4a0f-a40d-740e9fb56af3

import Definitions.Def_DeletionCode_FinitePairUnion
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_ExceptionalCountArithmetic

set_option autoImplicit true
open DeletionCode DeletionCode.ExceptionalCountArithmetic
open scoped BigOperators
namespace DeletionCode.ExceptionalCountArithmetic
theorem _root_.solution {t : ℕ} (ht : 1 ≤ t) :
    0 < exceptionalConstant t := by
  unfold exceptionalConstant
  apply Nat.mul_pos
  · omega
  · positivity
end DeletionCode.ExceptionalCountArithmetic
