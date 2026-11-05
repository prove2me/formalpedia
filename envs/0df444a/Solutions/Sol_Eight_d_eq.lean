-- Prove2me | solution 1 for Eight.d_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:46:43.350144+00:00
-- url     : https://prove2.me/submissions/095dba15-3882-4e0d-861c-27556849b7d6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Eight_SecCrossing_Identity
import Theorems.Thm_Eight_bxor_assoc
import Theorems.Thm_Eight_bxor_bxor_cancel
import Theorems.Thm_Eight_bxor_cancel_left

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution {p q p' q' : Block} (h : bxor p q = bxor p' q') : bxor q q' = bxor p p' :=
  calc bxor q q' = bxor (bxor p (bxor p q)) q' := by rw [bxor_cancel_left]
    _ = bxor p (bxor (bxor p' q') q') := by rw [h, bxor_assoc]
    _ = bxor p p' := by rw [bxor_bxor_cancel]
end Eight
