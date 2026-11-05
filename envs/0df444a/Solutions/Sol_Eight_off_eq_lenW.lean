-- Prove2me | solution 1 for Eight.off_eq_lenW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:28:28.992819+00:00
-- url     : https://prove2.me/submissions/49a826fb-4a33-4333-834e-8e699b62e306

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
theorem _root_.solution (tr : Bool) (Q : List Bool) (s : ℕ) : off tr Q s = lenW tr Q s := rfl
end Eight
