-- Prove2me | solution 1 for ClauseBound.Gen.Rate.zeta_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:34:42.427949+00:00
-- url     : https://prove2.me/submissions/0a5b5aa3-29ab-42e9-adbf-0d89894be0b0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_RateAux
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_ClauseBound_Gen_Rate

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace ClauseBound.Gen.Rate
theorem _root_.solution (l : ℕ) : zeta l ≤ 1 / 32 := by
  unfold zeta
  apply one_div_le_one_div_of_le (by norm_num)
  calc (32 : ℝ) = 2 ^ 5 := by norm_num
    _ ≤ 2 ^ (l + 5) := pow_le_pow_right₀ (by norm_num) (by omega)
end ClauseBound.Gen.Rate
