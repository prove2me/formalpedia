-- Prove2me | solution 1 for Eight.signs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:50:53.407037+00:00
-- url     : https://prove2.me/submissions/efe0437f-b056-4ead-af93-e3675428e0ab

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
import Theorems.Thm_Eight_d_ne_zero
import Theorems.Thm_P2M_Eight_p__eq_750c2ead4896
import Theorems.Thm_P2M_Eight_q__eq_27d0ba6cca4c
import Theorems.Thm_Eight_four_phi_odd
import Theorems.Thm_Eight_neg_one_pow_add_neg_one_pow

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution : Signs := by
  intro p q p' q' h hq
  have hodd := four_phi_odd p q (d_ne_zero hq)
  rw [← p'_eq h, ← q'_eq q q'] at hodd
  unfold sigma
  rw [← pow_add, ← pow_add]
  exact neg_one_pow_add_neg_one_pow (by rwa [← add_assoc])
end Eight
