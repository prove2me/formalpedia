-- Prove2me | solution 1 for ClauseBound.Gen.Rate.big_le_K
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:47:58.193051+00:00
-- url     : https://prove2.me/submissions/8d6e6beb-7ac0-4f1f-91d4-66b4478b3d8d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_RateAux
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_ClauseBound_Gen_Rate
import Theorems.Thm_ClauseBound_Gen_Rate_pow_le_K

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace ClauseBound.Gen.Rate
theorem _root_.solution (hx : 18 ≤ x₀) (l : ℕ) : 2 ^ 18 ≤ K x₀ l :=
  le_trans (Nat.pow_le_pow_right (by norm_num) hx) (pow_le_K hx l)
end ClauseBound.Gen.Rate
