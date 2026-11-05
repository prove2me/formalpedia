-- Prove2me | solution 1 for Eight.four_phi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:47:49.526447+00:00
-- url     : https://prove2.me/submissions/07b9f473-4ea7-4a6c-894a-1c7b2e7b1e3a

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
import Theorems.Thm_Eight_phi_add_phi_bxor

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution (p q d : Block) :
    phi p q + phi (bxor p d) (bxor q d) + phi p (bxor q d) + phi (bxor p d) q ≡ phi p d + phi (bxor p d) d [MOD 2] := by
  have h1 := phi_add_phi_bxor p q d
  have h2 := phi_add_phi_bxor (bxor p d) q d
  unfold Nat.ModEq at *
  omega
end Eight
