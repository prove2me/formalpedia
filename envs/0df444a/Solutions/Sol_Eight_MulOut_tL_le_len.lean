-- Prove2me | solution 1 for Eight.MulOut.tL_le_len
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:08:43.645247+00:00
-- url     : https://prove2.me/submissions/f0eb7712-9153-4d53-b644-5867dddcb92e

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
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_length_le_len
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Eight
open Groundwork PaddedDescent.F Finset Polynomial
namespace Eight
namespace MulOut
theorem _root_.solution (q : FourL) : tL q ≤ len q := by
  have h1 : tL q ≤ q.1.length := by unfold tL tOf; omega
  have h2 := length_le_len q.1
  have h3 : len q = len q.1 + len q.2 + 2 := len_pair q.1 q.2
  omega
end MulOut
end Eight
