-- Prove2me | solution 1 for DeletionCode.ExceptionalCountArithmetic.combined_records_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:05.880566+00:00
-- url     : https://prove2.me/submissions/37340fce-0e3a-4b77-8662-7ad8aacacb81

import Definitions.Def_DeletionCode_FinitePairUnion
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_ExceptionalCountArithmetic
import Theorems.Thm_DeletionCode_ExceptionalCountArithmetic_short_records_bound

set_option autoImplicit true
open DeletionCode DeletionCode.ExceptionalCountArithmetic
open scoped BigOperators
namespace DeletionCode.ExceptionalCountArithmetic
theorem _root_.solution (n t L : ℕ) (hn : 1 ≤ n) (hL : 1 ≤ L) :
    (∑ d ∈ Finset.range t, n ^ (2 * d) * 4 ^ (2 * d)) +
        (2 * t) * (2 * t + 2) * (2 * (4 * L)) * n ^ (2 * t - 1) * 4 ^ (2 * t) ≤
      exceptionalConstant t * L * n ^ (2 * t - 1) := by
  have hs := short_records_bound n t hn
  have hsL : t * 4 ^ (2 * t) * n ^ (2 * t - 1) ≤
      t * 4 ^ (2 * t) * n ^ (2 * t - 1) * L :=
    Nat.le_mul_of_pos_right _ hL
  calc
    _ ≤ t * 4 ^ (2 * t) * n ^ (2 * t - 1) * L +
        (2 * t) * (2 * t + 2) * (2 * (4 * L)) * n ^ (2 * t - 1) * 4 ^ (2 * t) :=
      Nat.add_le_add_right (hs.trans hsL) _
    _ = _ := by unfold exceptionalConstant; ring
end DeletionCode.ExceptionalCountArithmetic
