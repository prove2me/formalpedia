-- Prove2me | solution 1 for CliqueLevels.Proof.K_le_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:06:19.312657+00:00
-- url     : https://prove2.me/submissions/33a2e714-572e-4069-9f4f-08f7e7cb3b35

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
import Theorems.Thm_CliqueLevels_Proof_K_pos

set_option autoImplicit false
section
section
open CliqueLevels CliqueLevels.Proof
open Groundwork Printed
namespace CliqueLevels.Proof
theorem _root_.solution (x₀ l : ℕ) : Levels.Gen.K x₀ l ≤ Levels.Gen.K x₀ (l + 1) := by
  have h1 : 0 < 2 ^ (3 * l + x₀) := Nat.two_pow_pos _
  have h2 := K_pos x₀ l
  calc Levels.Gen.K x₀ l ≤ 2 ^ (3 * l + x₀) * Levels.Gen.K x₀ l := Nat.le_mul_of_pos_left _ h1
    _ ≤ (2 ^ (3 * l + x₀) * Levels.Gen.K x₀ l) ^ 2 := Nat.le_self_pow (by norm_num) _
end CliqueLevels.Proof
