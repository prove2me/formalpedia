-- Prove2me | solution 1 for Eight.Level.stPieces_of_lemPieces
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:17:39.187462+00:00
-- url     : https://prove2.me/submissions/3ca9135e-876f-4fd7-b554-82f8816692ea

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Level_Defs
import Definitions.Def_SingleBitPieces_Level_Pieces
import Mathlib.Tactic
import Definitions.Def_Eight_Level_Pieces
import Theorems.Thm_Eight_Level_stPieces_of

set_option autoImplicit false
section
section
open Eight Eight.Level
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Finset
namespace Eight.Level
theorem _root_.solution (h2 : LemPieces) (hF : StFact) : StPieces := stPieces_of hF h2.a_sum h2.a_abs
end Eight.Level
