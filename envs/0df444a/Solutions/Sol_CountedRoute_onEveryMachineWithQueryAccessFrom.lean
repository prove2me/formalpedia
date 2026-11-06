-- Prove2me | solution 1 for CountedRoute.onEveryMachineWithQueryAccessFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:01:58.478482+00:00
-- url     : https://prove2.me/submissions/ef6b4206-2464-4756-a5c5-c089257fbdfe

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
import Theorems.Thm_ThmVariables_numberBetween_cut


set_option autoImplicit false
section
section
open CountedRoute
open Turing Groundwork PaddedDescent.F ClauseBound.Alg QueryMachines QueryMachines.Bridge Printed CliqueLevels MainTheoremForms PairsToBound MainRoute NamesInOrder
open Sat3 (CNF)
namespace CountedRoute
theorem _root_.solution : OnEveryMachineWithQueryAccessFrom := by
  intro hB hCut hBoth hOn K e C₀ kf num E _ hyp
  obtain ⟨hP, Q, -, hK, hpick⟩ := hB E K e C₀ kf num hyp.solves hyp.levels hyp.computesK hyp.number
  have hnb := ThmVariables.numberBetween_cut Q hyp.number.1 hK
  obtain ⟨n₀, hn₀⟩ := hOn _ (solverOfMachine E num C₀) (cutNumber K num) (2 * C₀ + 1) Q hP (cutFraction num) hnb
  obtain ⟨n₀', hn₀'⟩ := hBoth _ (solverOfMachine E num C₀) (cutNumber K num) (2 * C₀ + 1) Q hP (cutFraction num) hnb
  refine ⟨max n₀ n₀', fun a ha n₁ hn₁ => ?_⟩
  have ha' : ∀ l : ℕ, cutNumber K num l ≤ ((2 * a : ℕ) : ℝ) / Real.sqrt (lg ((solverOfMachine E num C₀).K (Q.idx l))) := fun l => by
    rw [hK l]
    have h1 := ((hCut K e C₀ num hyp.levels hyp.number).2 l).2.2.1
    have h2 := ha l
    have h3 : ((2 * a : ℕ) : ℝ) / Real.sqrt (lg (K l)) = 2 * ((a : ℝ) / Real.sqrt (lg (K l))) := by
      push_cast
      ring
    rw [h3]
    linarith
  obtain ⟨r1, r2, r3⟩ := hn₀ (2 * a) ha' n₁ (le_trans (le_max_left _ _) hn₁)
  have r0 := ((hn₀' (2 * a) ha').2 n₁ (le_trans (le_max_right _ _) hn₁)).db
  rw [hpick] at r0 r1 r2 r3
  rw [hK 0] at r0 r2 r3
  exact ⟨r0, r1, r2, r3⟩
end CountedRoute
