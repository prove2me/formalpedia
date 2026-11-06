-- Prove2me | solution 1 for CliqueLevels.Proof.roundUnder_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:59:40.313217+00:00
-- url     : https://prove2.me/submissions/d3b1ec1b-6bf7-441a-862f-a2b3048f59cb

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
theorem _root_.solution {b : ℕ} {s : Option (ℕ × ℕ)} {pk : ℕ × ℕ} (h : roundUnder b s = some pk) : pk.2 ≤ b := by
  cases s with
  | none => cases h
  | some q =>
    change (if (q.1 * q.2) ^ 2 ≤ b then some (8 * q.1, (q.1 * q.2) ^ 2) else none) = some pk at h
    by_cases hq : (q.1 * q.2) ^ 2 ≤ b
    · rw [if_pos hq] at h
      obtain rfl := Option.some.inj h
      exact hq
    · rw [if_neg hq] at h
      cases h
end CliqueLevels.Proof
