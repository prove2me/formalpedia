-- Prove2me | solution 1 for Eight.sum_psi_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:16:04.629064+00:00
-- url     : https://prove2.me/submissions/a45958bf-2334-4547-a024-cb869947cdab

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
theorem _root_.solution (p q p' q' : Block) : ∑ k, psi k p q * psi k p' q' = if bxor p q = bxor p' q' then sigma p q * sigma p' q' else 0 := by
  rw [Finset.sum_eq_single (bxor p q)]
  · by_cases h : bxor p q = bxor p' q'
    · simp [psi, h]
    · simp [psi, h, Ne.symm h]
  · intro k _ hk
    simp [psi, Ne.symm hk]
  · simp
end Eight
