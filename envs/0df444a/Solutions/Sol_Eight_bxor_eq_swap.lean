-- Prove2me | solution 1 for Eight.bxor_eq_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:49:22.761974+00:00
-- url     : https://prove2.me/submissions/014fb231-9473-4060-b99f-b3627c431a8e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Blocks
import Theorems.Thm_Eight_bxor_eq_iff_zero
import Theorems.Thm_P2M_Eight_bxor_eq_iff_zero__40e241d4e138

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution (x y u v : Block) : bxor x y = bxor v u ↔ bxor x u = bxor v y :=
  (bxor_eq_iff_zero x y u v).trans (bxor_eq_iff_zero' x y u v).symm
end Eight
