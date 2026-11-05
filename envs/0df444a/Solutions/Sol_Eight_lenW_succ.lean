-- Prove2me | solution 1 for Eight.lenW_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:09:36.481588+00:00
-- url     : https://prove2.me/submissions/8d9d8dc8-04cc-4dea-aaa8-1dbf52530477

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_FactDefs
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Chunk

set_option autoImplicit false
section
section
open Eight
open Groundwork Groundwork.Prog PaddedDescent.F Finset
namespace Eight
theorem _root_.solution (tr : Bool) (Q : List Bool) (t : ℕ) : lenW tr Q (t + 1) = lenW tr Q t + if wide tr Q t = true then 6 else 3 := by
  unfold lenW
  rw [List.range_succ, List.countP_append, List.countP_singleton]
  split_ifs <;> omega
end Eight
