-- Prove2me | solution 1 for Eight.bitAt_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:49:29.469538+00:00
-- url     : https://prove2.me/submissions/14cfc937-5603-4280-86e9-d02760dcfbd1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_Blocks
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_PiecesAC

set_option autoImplicit false
section
section
open Eight
open Finset Polynomial
namespace Eight
theorem _root_.solution {lam : ℕ} (x : Pieces.Bits lam) (j : Fin lam) : bitAt x j = x j := by simp [bitAt]
end Eight
