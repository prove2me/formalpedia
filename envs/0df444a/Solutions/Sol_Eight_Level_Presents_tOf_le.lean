-- Prove2me | solution 1 for Eight.Level.Presents.tOf_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:10:17.22362+00:00
-- url     : https://prove2.me/submissions/f10d6d80-5299-4ae9-beaf-c7f7fd65a297

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Level_Defs
import Definitions.Def_SingleBitPieces_Level_Presents
import Mathlib.Tactic
import Definitions.Def_Eight_Level_Presents

set_option autoImplicit false
section
section
open Eight Eight.Level
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Stepped SingleBitPieces.Level.Presents
open Eight.Level.Presents
namespace Eight.Level.Presents
theorem _root_.solution (lam : ℕ) : tOf lam ≤ lam := by unfold tOf; omega
end Eight.Level.Presents
