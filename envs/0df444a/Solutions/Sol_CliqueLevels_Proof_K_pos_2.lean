-- Prove2me | solution 2 for CliqueLevels.Proof.K_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:59:35.165203+00:00
-- url     : https://prove2.me/submissions/a4523f9d-f627-4b2e-a485-37f05bcf0de5

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

set_option autoImplicit false
section
section
open CliqueLevels CliqueLevels.Proof
open Groundwork Printed
namespace CliqueLevels.Proof
theorem _root_.solution (x₀ l : ℕ) : 0 < Levels.Gen.K x₀ l := by
  cases l with
  | zero => exact Nat.two_pow_pos x₀
  | succ l => exact pow_pos (Nat.mul_pos (Nat.two_pow_pos _) (solution x₀ l)) 2
end CliqueLevels.Proof
