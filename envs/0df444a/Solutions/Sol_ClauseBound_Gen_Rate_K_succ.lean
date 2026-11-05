-- Prove2me | solution 1 for ClauseBound.Gen.Rate.K_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:16:51.349565+00:00
-- url     : https://prove2.me/submissions/ecaa1121-c320-42b6-ae6c-2fc578b53f7c

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
theorem _root_.solution (x₀ l : ℕ) : K x₀ (l + 1) = g x₀ l ^ 2 := rfl
end ClauseBound.Gen.Rate
