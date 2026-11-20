-- Prove2me | solution 1 for DeletionCode.UniqueWordParameters.uniquenessLength_eq_ceil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:11.081109+00:00
-- url     : https://prove2.me/submissions/15e7f370-5865-4753-b681-96d42ff98ef4

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_UniqueWordParameters
import Theorems.Thm_DeletionCode_UniqueWordParameters_uniquenessLength_eq_natCeil

set_option autoImplicit true
open DeletionCode DeletionCode.UniqueWordParameters
namespace DeletionCode.UniqueWordParameters
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) :
    (uniquenessLength n : ℤ) = 2 * ⌈Real.logb 2 (n : ℝ)⌉ + 2 := by
  rw [uniquenessLength_eq_natCeil]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [Int.natCast_ceil_eq_ceil
    (Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by exact_mod_cast hn))]
end DeletionCode.UniqueWordParameters
