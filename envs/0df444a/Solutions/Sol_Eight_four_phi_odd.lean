-- Prove2me | solution 1 for Eight.four_phi_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:50:07.24819+00:00
-- url     : https://prove2.me/submissions/f012f771-5813-4132-b72c-803ac5c1d2ad

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
import Theorems.Thm_Eight_four_phi
import Theorems.Thm_Eight_phi_add_phi_shift
import Theorems.Thm_Eight_four_changes
import Theorems.Thm_Eight_seven_terms
import Theorems.Thm_Eight_one_add_prod

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution (p q : Block) {d : Block} (h : d ≠ (false, false, false)) :
    Odd (phi p q + phi (bxor p d) (bxor q d) + phi p (bxor q d) + phi (bxor p d) q) :=
  Nat.odd_iff.2 ((four_phi p q d).trans ((phi_add_phi_shift p d).trans ((four_changes p d).trans ((seven_terms d).trans (one_add_prod h)))))
end Eight
