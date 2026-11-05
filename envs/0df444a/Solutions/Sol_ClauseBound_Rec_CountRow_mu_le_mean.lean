-- Prove2me | solution 1 for ClauseBound.Rec.CountRow.mu_le_mean
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:53:24.727394+00:00
-- url     : https://prove2.me/submissions/ca6dc45e-663c-4853-b00a-f1589a1b73a4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Rec_Blocks
import Definitions.Def_ClauseBound_Rec_Tail
import Definitions.Def_ClauseBound_Rec_CountRow
import Theorems.Thm_ClauseBound_Rec_CountRow_sum_odd

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Rec
open Finset Polynomial Pieces
open ClauseBound.Rec.CountRow
variable {n h : ℕ}
namespace ClauseBound.Rec.CountRow
theorem _root_.solution (n : ℕ) (hh : 1 ≤ h) : (mu n h : ℝ) ≤ mean n h := by
  have h1 : (mu n h : ℝ) ≤ ((∑ β : Lab n, odd h β : ℕ) : ℝ) / ((4 ^ n : ℕ) : ℝ) := Nat.cast_div_le
  rw [sum_odd n hh] at h1
  push_cast at h1
  rwa [mul_div_cancel_left₀ _ (by positivity)] at h1
end ClauseBound.Rec.CountRow
