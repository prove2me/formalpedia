-- Prove2me | solution 1 for Eight.topAt_append_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:08:47.168734+00:00
-- url     : https://prove2.me/submissions/a747e790-60df-4fa3-8f66-3bbf2d25b66b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_FactDefs
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Chunk
import Theorems.Thm_Eight_blkAt_append_left
import Theorems.Thm_Eight_off_eq_lenW
import Theorems.Thm_Eight_lenW_succ
import Theorems.Thm_Eight_lenW_mono
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Eight
open Groundwork Groundwork.Prog PaddedDescent.F Finset
namespace Eight
theorem _root_.solution (tr : Bool) (Q a b : List Bool) {u : List Bool} (v : List Bool) {s t : ℕ} (hs : s < t) (hu : u.length = lenW tr Q t) :
    topAt tr Q (u ++ v) a b s = topAt tr Q u a b s := by
  have h1 := lenW_mono tr Q (Nat.succ_le_of_lt hs)
  rw [Nat.succ_eq_add_one, lenW_succ] at h1
  unfold topAt
  rw [off_eq_lenW]
  split_ifs at h1 with hw
  · rw [blkAt_append_left v (by omega), blkAt_append_left v (by omega)]
  · rw [if_neg hw, if_neg hw, blkAt_append_left v (by omega)]
end Eight
