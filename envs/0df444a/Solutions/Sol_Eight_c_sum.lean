-- Prove2me | solution 1 for Eight.c_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:51:48.301977+00:00
-- url     : https://prove2.me/submissions/c169a8f6-894f-40e9-935c-b07552d4e4f4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_Blocks
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_PiecesAC
import Theorems.Thm_Eight_crow_add_ccol_le
import Theorems.Thm_Eight_eleven_tOf_le

set_option autoImplicit false
section
section
open Eight
open Finset Polynomial
namespace Eight
theorem _root_.solution : ∀ lam i : ℕ, 1 ≤ lam → i ≤ tOf lam → ((crow lam i + ccol lam i : ℕ) : ℝ) ≤ 4 * rho * lam + 8 := by
  intro lam i _ hi
  have h1 : ((crow lam i + ccol lam i : ℕ) : ℝ) ≤ 11 * tOf lam := by exact_mod_cast crow_add_ccol_le hi
  have h2 := eleven_tOf_le lam
  linarith [h2.1, h2.2]
end Eight
