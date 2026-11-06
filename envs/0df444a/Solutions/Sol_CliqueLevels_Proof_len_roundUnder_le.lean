-- Prove2me | solution 1 for CliqueLevels.Proof.len_roundUnder_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:59:45.962564+00:00
-- url     : https://prove2.me/submissions/d4566d41-213f-4cb6-8231-811536286254

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_GenLevelsDefs
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_ToTuring_Closure_Fold
import Definitions.Def_ToTuring_Closure_Cases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_CountedToPadded_GenLevels
import Theorems.Thm_Groundwork_PolyT_len_mul_le
import Theorems.Thm_Groundwork_RebalanceArith_size_le
import Theorems.Thm_Groundwork_len_nat_mono


set_option autoImplicit false
section
section
open CliqueLevels CliqueLevels.Proof
open Groundwork Printed
namespace CliqueLevels.Proof
theorem _root_.solution (b : ℕ) (s : Option (ℕ × ℕ)) : len (roundUnder b s) ≤ len s + (3 * b + 16) := by
  cases s with
  | none =>
    change len (none : Option (ℕ × ℕ)) ≤ _
    omega
  | some q =>
    change len (if (q.1 * q.2) ^ 2 ≤ b then some (8 * q.1, (q.1 * q.2) ^ 2) else none) ≤ _
    by_cases hq : (q.1 * q.2) ^ 2 ≤ b
    · rw [if_pos hq, len_some, len_some, len_pair]
      have e : len q = len q.1 + len q.2 + 2 := len_pair q.1 q.2
      have h1 := PolyT.len_mul_le 8 q.1
      have h2 := len_nat_mono hq
      have h3 : len (8 : ℕ) ≤ 14 := by
        rw [len_nat]
        have := Nat.size_le.2 (by norm_num : (8 : ℕ) < 2 ^ 4)
        omega
      have h4 : len b ≤ 3 * b + 2 := by
        rw [len_nat]
        have := Nat.size_le.2 (Nat.lt_two_pow_self (n := b))
        omega
      omega
    · rw [if_neg hq, len_none]
      omega
end CliqueLevels.Proof
