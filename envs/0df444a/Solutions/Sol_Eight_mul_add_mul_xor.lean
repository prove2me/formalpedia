-- Prove2me | solution 1 for Eight.mul_add_mul_xor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:45:53.144084+00:00
-- url     : https://prove2.me/submissions/7e814d6e-48ea-454e-a267-4ff8ebbb72a4

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

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution (c : ℕ) (a b : Bool) : c * a.toNat + c * (a ^^ b).toNat ≡ c * b.toNat [MOD 2] := by
  have h : c * a.toNat + c * (a ^^ b).toNat ≡ c * a.toNat + c * (a.toNat + b.toNat) [MOD 2] := ((toNat_xor a b).mul_left c).add_left _
  have e : c * a.toNat + c * (a.toNat + b.toNat) = 2 * (c * a.toNat) + c * b.toNat := by ring
  rw [e] at h
  unfold Nat.ModEq at *
  omega
end Eight
