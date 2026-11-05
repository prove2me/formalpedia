-- Prove2me | solution 1 for Eight.three_changes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:47:00.019109+00:00
-- url     : https://prove2.me/submissions/37615e26-12d5-42b7-8df0-dc2e575688c1

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
theorem _root_.solution (p d : Block) : chg1 p d + chg2 p d + chg3 p d
    = 2 * (p.1.toNat * d.2.1.toNat * d.2.2.toNat + p.2.1.toNat * d.1.toNat * d.2.2.toNat + p.2.2.toNat * d.1.toNat * d.2.1.toNat)
      + 3 * (d.1.toNat * d.2.1.toNat * d.2.2.toNat) := by
  unfold chg1 chg2 chg3; ring
end Eight
