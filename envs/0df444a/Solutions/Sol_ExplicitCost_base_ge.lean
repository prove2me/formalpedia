-- Prove2me | solution 1 for ExplicitCost.base_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:07:15.475397+00:00
-- url     : https://prove2.me/submissions/27f58c7d-8f3b-4ef6-a7c5-eac425b40771

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RecursionDefs
import Definitions.Def_Printed_Coding
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_StepMachines_Prog_SideBasics
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_EndBounds
import Theorems.Thm_ClauseBound_Gen_Rate_big_le_K


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution {x₀ : ℕ} (hx : 18 ≤ x₀) (l : ℕ) {lam B : ℕ} (hlam : 1 ≤ lam) (hB : 1 ≤ B) : (8 : ℝ) ≤ (Levels.Gen.K x₀ l : ℝ) * ((lam : ℝ) + B) := by
  have hK : (8 : ℝ) ≤ Levels.Gen.K x₀ l := by
    have := ClauseBound.Gen.Rate.big_le_K hx l
    exact_mod_cast (by omega : 8 ≤ Levels.Gen.K x₀ l)
  have h1 : (1 : ℝ) ≤ lam := by exact_mod_cast hlam
  have h2 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  nlinarith
end ExplicitCost
