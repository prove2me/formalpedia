-- Prove2me | solution 1 for ExplicitCost.patternValue_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:05:29.155394+00:00
-- url     : https://prove2.me/submissions/5464e98f-eec0-42ac-a93d-89f1b261f199

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CliqueReads
import Definitions.Def_CountedRecursion_SolverStages
import Definitions.Def_CountedRecursion_LevelNumbers
import Definitions.Def_Printed_GroupingEntry
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverPattern
import Theorems.Thm_ExplicitCost_askInt_within
import Theorems.Thm_ExplicitCost_mapIn_within
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Printed_AchievedBy_mono
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_mono
import Theorems.Thm_QueryMachines_QueryMachine_Runs_mono
import Theorems.Thm_QueryMachines_QueryMachine_WithinFrom_mono
import Theorems.Thm_QueryMachines_QueryMachine_Within_mono
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (hSub : QueryMachines.StSubstWithin) {c : ℕ} {O : SolQuery → Option Ans} {w : SolQuery → ℕ} {v : Ready × ℕ} {x tc T Sg : ℕ} {Z Zc : ℤ}
    (hG : ∀ O' : CliqueCall → Option ℤ, O' (callOf (searchInput c v, x)) = some Zc → groupingCall.Within O' (fun _ => tc + 2) (searchInput c v) T Sg Z)
    (hO : O (Sum.inl (child (v, callOf (searchInput c v, x)))) = some (.inl Zc)) (hw : w (Sum.inl (child (v, callOf (searchInput c v, x)))) = tc) :
    (patternValue c).Within O w v T (size v + Sg + (max (size (v, callOf (searchInput c v, x))) (size (Sum.inl Zc : Ans)) + 1) + 1) Z := by
  classical
  refine mapIn_within (g := fun v : Ready × ℕ => (v, searchInput c v)) ?_
  refine hSub CliqueCall ℤ SolQuery Ans (Ready × ℕ) GroupingInput ℤ groupingCall (askInt fun z : (Ready × ℕ) × CliqueCall => (Sum.inl (child z) : SolQuery))
    (fun z => if z = callOf (searchInput c v, x) then some Zc else none) O (fun _ => tc + 2) w v (searchInput c v) T Sg _ Z (fun _ => tc) (hG _ (if_pos rfl)) ?_ fun _ => le_rfl
  intro z u hz
  split_ifs at hz with hz'
  obtain rfl := Option.some.inj hz
  subst hz'
  exact (askInt_within (h := fun z : (Ready × ℕ) × CliqueCall => (Sum.inl (child z) : SolQuery)) (w := w) (a := (v, callOf (searchInput c v, x))) hO).mono hw.le le_rfl
end ExplicitCost
