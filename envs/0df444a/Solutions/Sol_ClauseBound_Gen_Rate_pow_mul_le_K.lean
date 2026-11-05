-- Prove2me | solution 1 for ClauseBound.Gen.Rate.pow_mul_le_K
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:34:12.879396+00:00
-- url     : https://prove2.me/submissions/dc190d3b-8c7b-4871-a321-0355866dfc95

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_RateAux
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_ClauseBound_Gen_Rate
import Theorems.Thm_ClauseBound_Gen_K_eq
import Theorems.Thm_ClauseBound_Gen_x_ge


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace ClauseBound.Gen.Rate
theorem _root_.solution (hx : 18 ≤ x₀) (l : ℕ) : 2 ^ x₀ * 2 ^ l ≤ K x₀ l := by
  rw [ClauseBound.Gen.K_eq, ← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by have := ClauseBound.Gen.x_ge x₀ l hx; omega)
end ClauseBound.Gen.Rate
