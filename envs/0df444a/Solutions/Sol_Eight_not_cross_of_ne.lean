-- Prove2me | solution 1 for Eight.not_cross_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:48:48.543526+00:00
-- url     : https://prove2.me/submissions/f4e9595f-9c31-4f51-a957-2ec0c07a9cf1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Blocks

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution {x y u v : Block} (h : bxor x y ≠ bxor v u) : ¬(x = v ∧ y = u) := fun ⟨h1, h2⟩ => h (by rw [h1, h2])
end Eight
