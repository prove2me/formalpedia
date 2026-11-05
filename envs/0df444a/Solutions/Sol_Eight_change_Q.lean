-- Prove2me | solution 1 for Eight.change_Q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:46:09.500749+00:00
-- url     : https://prove2.me/submissions/7f92c73b-c104-4452-be7c-5ac4a23e13ca

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Eight_SecCrossing_Identity
import Theorems.Thm_Eight_toNat_xor
import Theorems.Thm_Eight_modEq_of_eq

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution (p d : Block) : phiQ (bxor p d) d ≡ phiQ p d + phiQ d d [MOD 2] := by
  have h1 := toNat_xor p.1 d.1
  have h2 := toNat_xor p.2.1 d.2.1
  have h3 := toNat_xor p.2.2 d.2.2
  have h := (((((h1.mul_right d.1.toNat).add (h1.mul_right d.2.1.toNat)).add (h1.mul_right d.2.2.toNat)).add (h2.mul_right d.2.1.toNat)).add
    (h2.mul_right d.2.2.toNat)).add (h3.mul_right d.2.2.toNat)
  refine Nat.ModEq.trans h (modEq_of_eq ?_)
  unfold phiQ; ring
end Eight
