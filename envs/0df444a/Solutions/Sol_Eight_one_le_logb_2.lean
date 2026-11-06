-- Prove2me | solution 2 for Eight.one_le_logb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:53:55.417066+00:00
-- url     : https://prove2.me/submissions/c4072394-7065-42f2-964a-fec999e71e75

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
theorem _root_.solution {lam : ℕ} (hl : 1 ≤ lam) : (1 : ℝ) ≤ Real.logb 2 (2 * lam) := by
  have h : (1 : ℝ) ≤ lam := by exact_mod_cast hl
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith), Real.rpow_one]
  linarith
end Eight
