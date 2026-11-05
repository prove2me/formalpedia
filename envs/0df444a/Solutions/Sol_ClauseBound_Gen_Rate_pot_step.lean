-- Prove2me | solution 1 for ClauseBound.Gen.Rate.pot_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:38:41.486017+00:00
-- url     : https://prove2.me/submissions/dee796d9-a52d-4a90-be57-5fc832bb06e5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_RateAux
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_ClauseBound_Gen_Rate
import Theorems.Thm_ClauseBound_Gen_Rate_size_add_le
import Theorems.Thm_ClauseBound_Gen_Rate_size_mul_le
import Theorems.Thm_ClauseBound_Gen_Rate_size_two_mul_le
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace ClauseBound.Gen.Rate
theorem _root_.solution (z cnt nP a b d : ℕ) :
    Nat.size (z + a + Nat.size (cnt * nP) + b + d + 2 + Nat.size (cnt * nP)) ≤ Nat.size (z + Nat.size cnt) + 1 + Nat.size (a + b + d + 2 + 2 * Nat.size nP) := by
  have h := size_mul_le cnt nP
  have h1 : z + a + Nat.size (cnt * nP) + b + d + 2 + Nat.size (cnt * nP) ≤ 2 * (z + Nat.size cnt) + (a + b + d + 2 + 2 * Nat.size nP) := by omega
  have h2 := size_two_mul_le (z + Nat.size cnt)
  exact (Nat.size_le_size h1).trans ((size_add_le _ _).trans (by omega))
end ClauseBound.Gen.Rate
