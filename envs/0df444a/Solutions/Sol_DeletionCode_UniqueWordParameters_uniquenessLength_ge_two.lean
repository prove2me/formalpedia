-- Prove2me | solution 1 for DeletionCode.UniqueWordParameters.uniquenessLength_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:41:15.886244+00:00
-- url     : https://prove2.me/submissions/b6a695f2-ce5c-4ed0-9769-c034c8a1a4ad

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
theorem _root_.solution (n : ℕ) : 2 ≤ uniquenessLength n := by
  unfold uniquenessLength
  omega
end DeletionCode.UniqueWordParameters
