-- Prove2me | solution 1 for CliqueLevels.Proof.fold_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:12:38.675211+00:00
-- url     : https://prove2.me/submissions/69f794ff-8b51-42d9-a349-aad31404b519

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
import Theorems.Thm_CliqueLevels_Proof_K_le_succ
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open CliqueLevels CliqueLevels.Proof
open Groundwork Printed
namespace CliqueLevels.Proof
theorem _root_.solution (x₀ b l : ℕ) : (unary l).foldl (fun s _ => roundUnder b s) (if 2 ^ x₀ ≤ b then some (2 ^ x₀, 2 ^ x₀) else none) =
    if Levels.Gen.K x₀ l ≤ b then some (2 ^ (3 * l + x₀), Levels.Gen.K x₀ l) else none := by
  induction l with
  | zero =>
    change (if 2 ^ x₀ ≤ b then some (2 ^ x₀, 2 ^ x₀) else none) = if 2 ^ x₀ ≤ b then some (2 ^ (3 * 0 + x₀), 2 ^ x₀) else none
    rw [Nat.mul_zero, Nat.zero_add]
  | succ l ih =>
    have e : unary (l + 1) = unary l ++ [()] := List.replicate_succ'
    rw [e, List.foldl_append, ih]
    change roundUnder b _ = _
    have hK : Levels.Gen.K x₀ (l + 1) = (2 ^ (3 * l + x₀) * Levels.Gen.K x₀ l) ^ 2 := rfl
    by_cases h : Levels.Gen.K x₀ l ≤ b
    · rw [if_pos h]
      change (if (2 ^ (3 * l + x₀) * Levels.Gen.K x₀ l) ^ 2 ≤ b then some (8 * 2 ^ (3 * l + x₀), (2 ^ (3 * l + x₀) * Levels.Gen.K x₀ l) ^ 2) else none) = _
      have e8 : 8 * 2 ^ (3 * l + x₀) = 2 ^ (3 * (l + 1) + x₀) := by
        have h3 : 3 * (l + 1) + x₀ = 3 + (3 * l + x₀) := by ring
        calc 8 * 2 ^ (3 * l + x₀) = 2 ^ 3 * 2 ^ (3 * l + x₀) := by norm_num
          _ = 2 ^ (3 + (3 * l + x₀)) := (pow_add 2 3 _).symm
          _ = 2 ^ (3 * (l + 1) + x₀) := by rw [h3]
      rw [e8, hK]
    · rw [if_neg h, if_neg fun h' => h ((K_le_succ x₀ l).trans h')]
      rfl
end CliqueLevels.Proof
