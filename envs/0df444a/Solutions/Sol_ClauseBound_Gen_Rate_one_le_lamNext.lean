-- Prove2me | solution 1 for ClauseBound.Gen.Rate.one_le_lamNext
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:47:27.731704+00:00
-- url     : https://prove2.me/submissions/e7f44d25-457a-4236-8c46-4e81c0402859

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
theorem _root_.solution (P : PiecesF) (s : Step) (lam : ℕ) : 1 ≤ lamNextG P s lam := by
  unfold lamNextG; exact Nat.le_add_left 1 _
end ClauseBound.Gen.Rate
