-- Prove2me | solution 1 for Eight.two_mul_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:41:38.975642+00:00
-- url     : https://prove2.me/submissions/2cbb699a-2f33-445c-bf8d-3a9a8970b3c3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Tactic
import Definitions.Def_Eight_App_Pieces

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution (lam : ℕ) {c : ℕ} (hc : 1 ≤ c) : 2 * lam ≤ (2 * lam) ^ c :=
  Nat.le_self_pow (by omega) _
end Eight
