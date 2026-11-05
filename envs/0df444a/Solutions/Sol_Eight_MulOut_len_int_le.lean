-- Prove2me | solution 1 for Eight.MulOut.len_int_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:08:32.372672+00:00
-- url     : https://prove2.me/submissions/77ba6a15-c6ce-4c8b-87b4-35fe98bcb4d9

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

set_option autoImplicit false
section
section
open Eight
open Groundwork PaddedDescent.F Finset Polynomial
namespace Eight
namespace MulOut
theorem _root_.solution {z : ℤ} {n : ℕ} (h : |z| ≤ 2 ^ n) : len z ≤ 3 * n + 8 := by
  have h1 : z.natAbs < 2 ^ (n + 1) := by
    have : (z.natAbs : ℤ) ≤ 2 ^ n := by rwa [Int.natCast_natAbs]
    have h2 : z.natAbs ≤ 2 ^ n := by exact_mod_cast this
    rw [pow_succ]
    have := Nat.two_pow_pos n
    omega
  have h2 := Nat.size_le.2 h1
  rw [len_int]
  omega
end MulOut
end Eight
