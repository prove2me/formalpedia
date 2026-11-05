-- Prove2me | solution 1 for Eight.c_col
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:49:34.551204+00:00
-- url     : https://prove2.me/submissions/4579ff36-5925-4a4c-b7c5-101a697e32c6

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
theorem _root_.solution : ∀ lam i : ℕ, 1 ≤ lam → i ≤ tOf lam → ccol lam i ≤ 2 * lam := fun _ _ _ _ => min_le_left _ _
end Eight
