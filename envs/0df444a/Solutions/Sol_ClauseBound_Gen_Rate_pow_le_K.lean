-- Prove2me | solution 1 for ClauseBound.Gen.Rate.pow_le_K
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:41:04.358693+00:00
-- url     : https://prove2.me/submissions/e602408b-df13-4a92-88b3-b7075d5f78ab

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_RateAux
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_ClauseBound_Gen_Rate
import Theorems.Thm_ClauseBound_Gen_Rate_pow_mul_le_K

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace ClauseBound.Gen.Rate
theorem _root_.solution (hx : 18 ≤ x₀) (l : ℕ) : 2 ^ x₀ ≤ K x₀ l :=
  le_trans (Nat.le_mul_of_pos_right _ (by positivity)) (pow_mul_le_K hx l)
end ClauseBound.Gen.Rate
