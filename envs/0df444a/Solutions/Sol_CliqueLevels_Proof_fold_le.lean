-- Prove2me | solution 1 for CliqueLevels.Proof.fold_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:07:04.104552+00:00
-- url     : https://prove2.me/submissions/f61a6cc9-d884-427c-9cd4-3829b89dd071

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
import Theorems.Thm_CliqueLevels_Proof_roundUnder_le

set_option autoImplicit false
section
section
open CliqueLevels CliqueLevels.Proof
open Groundwork Printed
namespace CliqueLevels.Proof
theorem _root_.solution (b : ℕ) (L : List Unit) (s : Option (ℕ × ℕ)) (hs : ∀ pk, s = some pk → pk.2 ≤ b) :
    ∀ pk, L.foldl (fun s _ => roundUnder b s) s = some pk → pk.2 ≤ b := by
  induction L generalizing s with
  | nil => exact hs
  | cons _ L ih => exact ih _ fun _ h => roundUnder_le h
end CliqueLevels.Proof
