-- Prove2me | solution 1 for Eight.Fact.abs_botAt_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:09:15.358192+00:00
-- url     : https://prove2.me/submissions/8b0935a3-77d5-4b53-b22d-3988f5d10d98

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_FactDefs
import Definitions.Def_Eight_SecCrossing_Blocks
import Definitions.Def_Eight_SecCrossing_Chunk
import Definitions.Def_Eight_SecCrossing_MulOut
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Fact
import Theorems.Thm_Eight_abs_Rb_le
import Theorems.Thm_Eight_abs_psi_le


set_option autoImplicit false
section
section
open Eight
open Groundwork Groundwork.Prog PaddedDescent.F Finset
open Eight.Fact
namespace Eight.Fact
theorem _root_.solution (tr : Bool) (Q w a b : List Bool) (s : ℕ) : |botAt tr Q w a b s| ≤ 1 := by
  unfold botAt
  split
  · exact abs_Rb_le _ _ _ _
  · exact abs_psi_le _ _ _
end Eight.Fact
