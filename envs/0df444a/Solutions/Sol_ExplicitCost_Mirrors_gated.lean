-- Prove2me | solution 1 for ExplicitCost.Mirrors.gated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:34:44.57977+00:00
-- url     : https://prove2.me/submissions/112d703b-b4d6-4a4b-b7cc-35bdc7b7acc5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombDefs
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_Mirror
import Theorems.Thm_ExplicitCost_Mirrors_mono
import Theorems.Thm_ExplicitCost_mirrors_const
import Theorems.Thm_ExplicitCost_Mirrors_mapIn
import Theorems.Thm_ExplicitCost_Mirrors_ite
import Theorems.Thm_ExplicitCost_Mirrors_bind
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_mono
import Theorems.Thm_QueryMachines_QueryMachine_Runs_mono
import Theorems.Thm_QueryMachines_QueryMachine_WithinFrom_mono
import Theorems.Thm_QueryMachines_QueryMachine_Within_mono
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines
variable {Q A α α' α₁ α₁' α₂ α₂' β β' γ τ τ' : Type}
namespace ExplicitCost
namespace Mirrors
theorem _root_.solution [HasSize α] [HasSize α'] {M : QueryMachine Q A α Bool} {M' : QueryMachine Q A α' Bool} {N : QueryMachine Q A α ℤ} {N' : QueryMachine Q A α' ℤ} {w : α → α'} {d₁ d₂ dw d : ℕ}
    (hM : Mirrors M M' w d₁) (hN : Mirrors N N' w d₂) (hw : ∀ a, size (w a) ≤ size a + dw) (h1 : dw + d₁ ≤ d) (h2 : d₂ ≤ d) :
    Mirrors (QueryMachine.gated M N) (QueryMachine.gated M' N') w d :=
  Mirrors.bind hM
    (Mirrors.ite ((hN.mapIn (w := Prod.map w id) fun _ => rfl).mono h2)
      (mirrors_const 0 fun p : α × Bool => by
        change size (w p.1) + size p.2 ≤ size p.1 + size p.2 + d
        have := hw p.1
        omega) fun _ => rfl)
    hw h1 le_rfl
end Mirrors
end ExplicitCost
