-- Prove2me | solution 1 for Eight.eleven_tOf_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:50:41.239815+00:00
-- url     : https://prove2.me/submissions/7cc2cbfa-11ef-4f18-af5d-9033b9a76fb2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_Blocks
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_PiecesAC
import Theorems.Thm_Eight_three_mul_tOf_le

set_option autoImplicit false
section
section
open Eight
open Finset Polynomial
namespace Eight
theorem _root_.solution (lam : ℕ) : (11 * tOf lam : ℝ) ≤ 11 * lam / 3 + 8 ∧ (11 * lam / 3 + 8 : ℝ) = 4 * rho * lam + 8 := by
  have h : (3 * tOf lam : ℝ) ≤ lam + 2 := by exact_mod_cast three_mul_tOf_le lam
  constructor
  · linarith
  · unfold rho; ring
end Eight
