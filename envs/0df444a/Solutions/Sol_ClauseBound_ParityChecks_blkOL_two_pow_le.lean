-- Prove2me | solution 1 for ClauseBound.ParityChecks.blkOL_two_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:31:10.923631+00:00
-- url     : https://prove2.me/submissions/35e4ce53-8098-45ac-b83d-e8bae7c5c721

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Params
import Definitions.Def_ClauseBound_ParityChecks_ArithAux
import Theorems.Thm_ClauseBound_ParityChecks_LD_two_pow

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
namespace ClauseBound.ParityChecks
theorem _root_.solution (β : ℕ) : blkOL (2 ^ β) ≤ 2 ^ (2 * β + 5) := by
  rw [blkOL, LD_two_pow]
  have h1 : β + 1 ≤ 2 ^ β := Nat.lt_two_pow_self
  have h2 : 1 ≤ 2 ^ β := Nat.one_le_two_pow
  have e : 2 ^ (2 * β + 5) = 32 * (2 ^ β * 2 ^ β) := by
    rw [show 2 * β + 5 = β + β + 5 by ring, pow_add, pow_add]; ring
  rw [e]
  generalize 2 ^ β = E at *
  have h3 : 16 * E * (β + 1) ≤ 16 * E * E := Nat.mul_le_mul_left _ h1
  have h4 : E ≤ E * E := Nat.le_mul_of_pos_left _ h2
  nlinarith
end ClauseBound.ParityChecks
