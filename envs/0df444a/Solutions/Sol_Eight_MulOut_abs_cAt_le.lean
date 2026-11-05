-- Prove2me | solution 1 for Eight.MulOut.abs_cAt_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:08:24.017192+00:00
-- url     : https://prove2.me/submissions/927bf030-c3c0-4653-bd0a-b56f29936a32

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
import Theorems.Thm_Eight_abs_Cb_le


set_option autoImplicit false
section
section
open Eight
open Groundwork PaddedDescent.F Finset Polynomial
namespace Eight
namespace MulOut
theorem _root_.solution (q : FourL) (s : ℕ) : |cAt q s| ≤ 1 := abs_Cb_le _ _ _ _
end MulOut
end Eight
