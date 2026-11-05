-- Prove2me | solution 1 for Eight.Level.patOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:11:34.606782+00:00
-- url     : https://prove2.me/submissions/6671fbf2-36d6-43c3-86b1-8a9bebc56626

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecLevel_Grid
import Definitions.Def_Eight_Level_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_SecLevel_GridWords
import Theorems.Thm_Paper_mem_rectangles


set_option autoImplicit false
section
section
open Eight Eight.Level
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet
open Paper (Rectangle rectangles mem_rectangles FactorsThrough)
variable {g lam : ℕ}
namespace Eight.Level
theorem _root_.solution (g lam y : ℕ) {q : Rectangle g} (hq : q ∈ rectangles g) : Eight.Level.patOf g lam y q = digOf g lam y q := if_pos hq
end Eight.Level
