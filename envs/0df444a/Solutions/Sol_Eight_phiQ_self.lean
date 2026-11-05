-- Prove2me | solution 1 for Eight.phiQ_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:48:13.273181+00:00
-- url     : https://prove2.me/submissions/da820b39-3275-442c-8810-1bcf3d4f743b

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
import Theorems.Thm_Eight_toNat_mul_self

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution (d : Block) : phiQ d d
    = d.1.toNat + d.2.1.toNat + d.2.2.toNat + d.1.toNat * d.2.1.toNat + d.1.toNat * d.2.2.toNat + d.2.1.toNat * d.2.2.toNat := by
  unfold phiQ
  rw [toNat_mul_self d.1, toNat_mul_self d.2.1, toNat_mul_self d.2.2]
  ring
end Eight
