-- Prove2me | solution 1 for ClauseBound.Gen.Rate.Bd_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:35:07.484964+00:00
-- url     : https://prove2.me/submissions/11497757-9097-4664-b5c7-5e9cad9c5052

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
theorem _root_.solution (ρ : ℝ) (c x₀ l lam B : ℕ) : Bd ρ c x₀ (l + 1) lam B = e ρ x₀ (l + 1) * ((g x₀ l : ℝ) ^ 4 * lam) +
    (6 * c + 14) * (g x₀ l : ℝ) ^ 4 * Real.logb 2 ((K x₀ (l + 1) : ℝ) * (lam + B)) := by
  have h : (K x₀ (l + 1) : ℝ) ^ 2 = (g x₀ l : ℝ) ^ 4 := by rw [K_succ]; push_cast; ring
  unfold Bd; rw [h]; ring
end ClauseBound.Gen.Rate
