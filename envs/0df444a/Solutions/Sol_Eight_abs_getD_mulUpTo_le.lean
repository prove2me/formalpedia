-- Prove2me | solution 1 for Eight.abs_getD_mulUpTo_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:21:34.884184+00:00
-- url     : https://prove2.me/submissions/a8ad70d6-4fc6-45db-9184-b834324d14c6

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
import Theorems.Thm_Eight_abs_getD_mulUpTo_le_choose
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open Eight
open Groundwork PaddedDescent.F Finset Polynomial
namespace Eight
theorem _root_.solution (q : FourL) (n j : ℕ) : |(mulUpTo q n).getD j 0| ≤ 2 ^ n :=
  (abs_getD_mulUpTo_le_choose q n j).trans (by exact_mod_cast Nat.choose_le_two_pow n j)
end Eight
