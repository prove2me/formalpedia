-- Prove2me | solution 1 for Eight.lenW_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:17:47.053964+00:00
-- url     : https://prove2.me/submissions/5cce9a75-d34b-40e4-8d09-8be80f17c954

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_FactDefs
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Chunk
import Theorems.Thm_Eight_lenW_succ

set_option autoImplicit false
section
section
open Eight
open Groundwork Groundwork.Prog PaddedDescent.F Finset
namespace Eight
theorem _root_.solution (tr : Bool) (Q : List Bool) : Monotone (lenW tr Q) :=
  monotone_nat_of_le_succ fun t => by rw [lenW_succ]; omega
end Eight
