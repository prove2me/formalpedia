-- Prove2me | solution 1 for ClauseBound.Gen.Rate.pow_le_g
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:54:32.952639+00:00
-- url     : https://prove2.me/submissions/e3c6d2e5-5282-47d1-b803-b26db65dfa47

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_RateAux
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_ClauseBound_Gen_Rate
import Theorems.Thm_ClauseBound_Gen_Rate_big_le_K

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace ClauseBound.Gen.Rate
theorem _root_.solution (hx : 18 ≤ x₀) (l : ℕ) : 2 ^ (l + 5) ≤ g x₀ l := by
  unfold g
  calc 2 ^ (l + 5) ≤ 2 ^ (3 * l + x₀) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ 2 ^ (3 * l + x₀) * K x₀ l := Nat.le_mul_of_pos_right _ (by have := big_le_K hx l; omega)
end ClauseBound.Gen.Rate
