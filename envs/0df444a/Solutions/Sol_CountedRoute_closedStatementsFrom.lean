-- Prove2me | solution 1 for CountedRoute.closedStatementsFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:01:39.477132+00:00
-- url     : https://prove2.me/submissions/9f00f6ed-1f13-43ae-8f4b-4b1deeec243f

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
import Theorems.Thm_NamesInOrder_builtIsAssembledDirectly


set_option autoImplicit false
section
section
open CountedRoute
open Turing Groundwork PaddedDescent.F ClauseBound.Alg QueryMachines QueryMachines.Bridge Printed CliqueLevels MainTheoremForms PairsToBound MainRoute NamesInOrder
open Sat3 (CNF)
namespace CountedRoute
theorem _root_.solution : ClosedStatementsFrom := by
  rintro ⟨c, x₀, C₀, D, Alg, -, -, -, -, -, -, hyp, h⟩
  obtain ⟨inst⟩ := hyp.steps
  obtain ⟨n₀, hn₀⟩ := h
  obtain ⟨hVariablesB, hM, hN, N, hB⟩ := hn₀ n₀ le_rfl
  obtain ⟨hA, hf⟩ := builtIsAssembledDirectly _ _ _ _ _ _ hB
  obtain ⟨C, h12, h1⟩ := hN N hA
  obtain ⟨Ma, Mb, M₂, M₁, qa, qb, q₂, -, q₁, -, -, pre, test, -, -, -, -, -, -, hf₂, hf₁, -, -, -, hMa, hMb, hpre, htest, -, hch, hM₁, -⟩ := hB
  obtain ⟨C₁, hC₁⟩ := hM M₁ q₁ hM₁
  obtain ⟨C₂, hC₂⟩ := hVariablesB M₂ ⟨Ma, Mb, qa, qb, q₂, pre, test, hMa, hMb, hpre, htest, hch⟩
  exact ⟨⟨N, C, hf, h1⟩, ⟨N, C, hf, h12⟩, ⟨M₂, C₂, hf₂, hC₂⟩, ⟨M₁, C₁, hf₁, hC₁⟩⟩
end CountedRoute
