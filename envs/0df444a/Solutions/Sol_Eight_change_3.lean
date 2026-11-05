-- Prove2me | solution 1 for Eight.change_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:46:53.84238+00:00
-- url     : https://prove2.me/submissions/14b5f225-4985-4a2e-b7f1-19885c3f31d7

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
theorem _root_.solution (p d : Block) : phi3 (bxor p d) d ≡ phi3 p d + chg3 p d [MOD 2] := by
  refine Nat.ModEq.trans (((toNat_xor p.1 d.1).mul (toNat_xor p.2.1 d.2.1)).mul_right d.2.2.toNat) (modEq_of_eq ?_)
  unfold phi3 chg3; ring
end Eight
