-- Prove2me | solution 1 for CountedRoute.onTheCountedRecursionFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:01:08.244199+00:00
-- url     : https://prove2.me/submissions/793a985d-be72-48b2-8b16-636bbd7445ac

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRoute_Defs
import Definitions.Def_ThmVariables_PartA
import Definitions.Def_NamesInOrder_Main
import Definitions.Def_MainRoute_GeneralMain
import Definitions.Def_CountedToPadded_Main
import Definitions.Def_CountedToPadded_Need
import Definitions.Def_CountedInstance_Main
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_CountedRoute_Main
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_hyp


set_option autoImplicit false
section
section
open CountedRoute
open Turing Groundwork PaddedDescent.F ClauseBound.Alg QueryMachines QueryMachines.Bridge Printed CliqueLevels MainTheoremForms PairsToBound MainRoute NamesInOrder
open Sat3 (CNF)
namespace CountedRoute
theorem _root_.solution : OnTheCountedRecursionFrom := by
  rintro ⟨c, x₀, C₀, D, Alg, hPieces, hShort, hAppHalfPieces, hx, hc, hsteps, hsolves, hlev, hcomp, hnum, hrate⟩ hOn
  have hyp : ThmVariables.Hypothesis (_root_.Levels.Gen.K x₀) (_root_.Levels.Gen.e (1 / Real.sqrt 2) x₀) C₀ (levelsUnder x₀) fractionHalf (ExplicitCost.cliqueMachine (c + 2) x₀ Alg) :=
    ⟨hlev, hcomp, hnum, hsteps, hsolves⟩
  refine ⟨c, x₀, C₀, D, Alg, hPieces, hShort, hAppHalfPieces, hx, hc, hrate, hyp, ?_⟩
  intro inst
  obtain ⟨n₀, hn₀⟩ := hOn _ _ C₀ _ _ (ExplicitCost.cliqueMachine (c + 2) x₀ Alg) hyp
  exact ⟨n₀, fun n₁ h => hn₀ (3 * x₀ + 6) hrate n₁ h⟩
end CountedRoute
