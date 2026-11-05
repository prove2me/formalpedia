-- Prove2me | solution 1 for Eight.four_changes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:49:24.487955+00:00
-- url     : https://prove2.me/submissions/0bea3854-99b9-4c1c-a618-a8888327a23d

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
import Theorems.Thm_Eight_three_changes
import Theorems.Thm_Eight_phiQ_self

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution (p d : Block) : phiQ d d + chg1 p d + chg2 p d + chg3 p d
    ≡ d.1.toNat + d.2.1.toNat + d.2.2.toNat + d.1.toNat * d.2.1.toNat + d.1.toNat * d.2.2.toNat + d.2.1.toNat * d.2.2.toNat
      + d.1.toNat * d.2.1.toNat * d.2.2.toNat [MOD 2] := by
  have h := three_changes p d
  rw [phiQ_self]
  unfold Nat.ModEq
  omega
end Eight
