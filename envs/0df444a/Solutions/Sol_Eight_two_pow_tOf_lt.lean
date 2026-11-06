-- Prove2me | solution 1 for Eight.two_pow_tOf_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:53:50.457282+00:00
-- url     : https://prove2.me/submissions/ec5573a9-6e41-4797-80bd-6b9666632f60

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Tactic
import Definitions.Def_Eight_App_Pieces
import Theorems.Thm_Eight_tOf_le
import Theorems.Thm_Eight_two_mul_le_pow

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution {lam c : ℕ} (hl : 1 ≤ lam) (hc : 1 ≤ c) : (2 : ℤ) ^ tOf lam < 2 ^ (2 * lam) ^ c := by
  have h1 := tOf_le hl
  have h2 := two_mul_le_pow lam hc
  exact pow_lt_pow_right₀ (by norm_num) (by omega)
end Eight
