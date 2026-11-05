-- Prove2me | solution 1 for ClauseBound.Gen.Rate.X_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:19:05.873209+00:00
-- url     : https://prove2.me/submissions/8df319e4-e75f-4787-87f1-585d3cfcd270

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_RateAux
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_ClauseBound_Gen_Rate
import Theorems.Thm_ClauseBound_Gen_Rate_K_succ

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace ClauseBound.Gen.Rate
theorem _root_.solution (x₀ l lam B : ℕ) : ((g x₀ l ^ 2 * (lam + B) : ℕ) : ℝ) = (K x₀ (l + 1) : ℝ) * (lam + B) := by
  rw [K_succ]; push_cast; ring
end ClauseBound.Gen.Rate
