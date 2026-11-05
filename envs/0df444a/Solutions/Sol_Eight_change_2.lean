-- Prove2me | solution 1 for Eight.change_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:46:29.619795+00:00
-- url     : https://prove2.me/submissions/866f3a88-a9dc-4c67-8356-8862f693eec9

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
theorem _root_.solution (p d : Block) : phi2 (bxor p d) d ≡ phi2 p d + chg2 p d [MOD 2] := by
  refine Nat.ModEq.trans (((toNat_xor p.1 d.1).mul_right d.2.1.toNat).mul (toNat_xor p.2.2 d.2.2)) (modEq_of_eq ?_)
  unfold phi2 chg2; ring
end Eight
