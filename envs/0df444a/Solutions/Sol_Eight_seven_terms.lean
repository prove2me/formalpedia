-- Prove2me | solution 1 for Eight.seven_terms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:47:30.035667+00:00
-- url     : https://prove2.me/submissions/0e995126-a21a-4b2e-ae00-604797040c6d

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

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution (d : Block) :
    d.1.toNat + d.2.1.toNat + d.2.2.toNat + d.1.toNat * d.2.1.toNat + d.1.toNat * d.2.2.toNat + d.2.1.toNat * d.2.2.toNat
      + d.1.toNat * d.2.1.toNat * d.2.2.toNat ≡ 1 + (1 + d.1.toNat) * (1 + d.2.1.toNat) * (1 + d.2.2.toNat) [MOD 2] := by
  have h : 1 + (1 + d.1.toNat) * (1 + d.2.1.toNat) * (1 + d.2.2.toNat)
      = 2 + (d.1.toNat + d.2.1.toNat + d.2.2.toNat + d.1.toNat * d.2.1.toNat + d.1.toNat * d.2.2.toNat + d.2.1.toNat * d.2.2.toNat
        + d.1.toNat * d.2.1.toNat * d.2.2.toNat) := by ring
  rw [h]
  unfold Nat.ModEq
  omega
end Eight
