-- Prove2me | solution 1 for ClauseBound.Rec.CountRow.mean_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:53:49.069008+00:00
-- url     : https://prove2.me/submissions/b71fb6c2-3300-4485-866a-cdbb1af01351

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
theorem _root_.solution (n : ℕ) (hh : 1 ≤ h) : mean n h < mu n h + 1 := by
  have h1 : (∑ β : Lab n, odd h β) < 4 ^ n * (mu n h + 1) := Nat.lt_mul_div_succ _ (by positivity)
  have h2 : ((∑ β : Lab n, odd h β : ℕ) : ℝ) < ((4 ^ n * (mu n h + 1) : ℕ) : ℝ) := by exact_mod_cast h1
  rw [sum_odd n hh] at h2
  push_cast at h2
  exact lt_of_mul_lt_mul_left h2 (by positivity)
end ClauseBound.Rec.CountRow
