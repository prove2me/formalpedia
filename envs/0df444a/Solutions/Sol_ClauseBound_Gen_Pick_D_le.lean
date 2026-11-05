-- Prove2me | solution 1 for ClauseBound.Gen.Pick.D_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:16:09.618211+00:00
-- url     : https://prove2.me/submissions/6ebc1059-ce4e-4315-bcd0-8de8ed654a1e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Gen_Pick
import Theorems.Thm_ClauseBound_Gen_Pick_two_pow_le

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Pick
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen
namespace ClauseBound.Gen.Pick
theorem _root_.solution (m x₀ l : ℕ) : 3 * m * 2 ^ (l + 4) ≤ 48 * (m * 2 ^ (3 * l + x₀)) := by
  have h : 3 * m * 2 ^ (l + 4) = 48 * (m * 2 ^ l) := by ring
  rw [h]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (two_pow_le x₀ l))
end ClauseBound.Gen.Pick
