-- Prove2me | solution 1 for Eight.phi_add_phi_bxor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:46:52.835775+00:00
-- url     : https://prove2.me/submissions/77f19cbc-da4d-4f5a-85be-d853f88f90b4

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
import Theorems.Thm_Eight_bxor_bit1
import Theorems.Thm_Eight_bxor_bit2
import Theorems.Thm_Eight_bxor_bit3
import Theorems.Thm_Eight_phi_linear
import Theorems.Thm_Eight_mul_add_mul_xor

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution (p q d : Block) : phi p q + phi p (bxor q d) ≡ phi p d [MOD 2] := by
  have h1 := mul_add_mul_xor (lin1 p) q.1 d.1
  have h2 := mul_add_mul_xor (lin2 p) q.2.1 d.2.1
  have h3 := mul_add_mul_xor (lin3 p) q.2.2 d.2.2
  rw [phi_linear p q, phi_linear p (bxor q d), phi_linear p d, bxor_bit1, bxor_bit2, bxor_bit3]
  unfold Nat.ModEq at *
  omega
end Eight
