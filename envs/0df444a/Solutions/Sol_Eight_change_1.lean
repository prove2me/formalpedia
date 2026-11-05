-- Prove2me | solution 1 for Eight.change_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:46:20.282013+00:00
-- url     : https://prove2.me/submissions/d1269560-4e75-484b-9bf9-70fd955ecb91

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
theorem _root_.solution (p d : Block) : phi1 (bxor p d) d ≡ phi1 p d + chg1 p d [MOD 2] := by
  refine Nat.ModEq.trans (((toNat_xor p.2.1 d.2.1).mul_left d.1.toNat).mul (toNat_xor p.2.2 d.2.2)) (modEq_of_eq ?_)
  unfold phi1 chg1; ring
end Eight
