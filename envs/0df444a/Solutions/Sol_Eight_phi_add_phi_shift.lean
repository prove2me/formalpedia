-- Prove2me | solution 1 for Eight.phi_add_phi_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:47:52.397831+00:00
-- url     : https://prove2.me/submissions/cb693ce7-cc6f-4e6a-90b7-4c56e220316c

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
import Theorems.Thm_Eight_phi_parts
import Theorems.Thm_Eight_change_Q
import Theorems.Thm_Eight_change_1
import Theorems.Thm_Eight_change_2
import Theorems.Thm_Eight_change_3

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution (p d : Block) : phi p d + phi (bxor p d) d ≡ phiQ d d + chg1 p d + chg2 p d + chg3 p d [MOD 2] := by
  have h0 := change_Q p d
  have h1 := change_1 p d
  have h2 := change_2 p d
  have h3 := change_3 p d
  rw [phi_parts, phi_parts]
  unfold Nat.ModEq at *
  omega
end Eight
