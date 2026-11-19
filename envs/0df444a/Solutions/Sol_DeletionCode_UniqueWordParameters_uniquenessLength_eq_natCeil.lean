-- Prove2me | solution 1 for DeletionCode.UniqueWordParameters.uniquenessLength_eq_natCeil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:41:19.694679+00:00
-- url     : https://prove2.me/submissions/a9909a3f-1025-4a11-a83f-8cbf1305b6b0

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
    uniquenessLength n = 2 * ⌈Real.logb 2 (n : ℝ)⌉₊ + 2 := by
  have hceil : ⌈Real.logb 2 (n : ℝ)⌉₊ = Nat.clog 2 n := by
    simpa only [Nat.cast_ofNat] using Real.natCeil_logb_natCast 2 n
  rw [hceil]
  rfl
end DeletionCode.UniqueWordParameters
