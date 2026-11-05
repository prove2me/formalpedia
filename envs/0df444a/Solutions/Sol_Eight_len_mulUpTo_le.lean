-- Prove2me | solution 1 for Eight.len_mulUpTo_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:31:31.99994+00:00
-- url     : https://prove2.me/submissions/b1b5eea4-7499-49b9-a046-daed927debeb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_PolyDefs
import Definitions.Def_Eight_SecCrossing_Blocks
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Eight_SecCrossing_MulOut
import Theorems.Thm_Eight_length_mulUpTo
import Theorems.Thm_Eight_abs_getD_mulUpTo_le
import Theorems.Thm_Eight_MulOut_len_listZ_le
import Theorems.Thm_Eight_MulOut_len_int_le

set_option autoImplicit false
section
section
open Eight
open Groundwork PaddedDescent.F Finset Polynomial
namespace Eight
theorem _root_.solution (q : FourL) (n : ℕ) : len (mulUpTo q n) ≤ (n + 1) * (3 * n + 10) + 2 := by
  have h := MulOut.len_listZ_le (3 * n + 8) (mulUpTo q n) fun z hz => by
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hz
    rw [← List.getD_eq_getElem _ 0 hj]
    exact MulOut.len_int_le (abs_getD_mulUpTo_le q n j)
  rwa [length_mulUpTo] at h
end Eight
