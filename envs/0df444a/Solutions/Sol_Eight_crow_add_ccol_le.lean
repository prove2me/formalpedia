-- Prove2me | solution 1 for Eight.crow_add_ccol_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:16:16.897554+00:00
-- url     : https://prove2.me/submissions/6c092a82-a5eb-475c-a557-6ce37eb36a27

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
theorem _root_.solution {lam i : ℕ} (hi : i ≤ tOf lam) : crow lam i + ccol lam i ≤ 11 * tOf lam := by
  have h1 : crow lam i ≤ 4 * tOf lam + 3 * i := min_le_right _ _
  have h2 : ccol lam i ≤ 7 * tOf lam - 3 * i := min_le_right _ _
  omega
end Eight
