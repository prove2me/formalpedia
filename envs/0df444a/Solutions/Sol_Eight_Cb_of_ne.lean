-- Prove2me | solution 1 for Eight.Cb_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:50:13.134547+00:00
-- url     : https://prove2.me/submissions/8ac4037e-cca3-42d9-85b9-e8d7d56872e0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Blocks
import Theorems.Thm_Eight_bxor_eq_swap
import Theorems.Thm_Eight_Cb_eq

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution {x y u v : Block} (h : bxor x y ≠ bxor v u) : Cb x y u v = 0 := by
  rw [Cb_eq, if_neg fun h' => h ((bxor_eq_swap x y u v).2 h')]
end Eight
