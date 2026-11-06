-- Prove2me | solution 1 for ExplicitCost.Mirrors.ite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:28:26.934844+00:00
-- url     : https://prove2.me/submissions/555dfae4-577e-45f1-9cb7-cb97fb2136a8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombDefs
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_Mirror
import Theorems.Thm_ExplicitCost_Mirrors_branch

set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines
variable {Q A α α' α₁ α₁' α₂ α₂' β β' γ τ τ' : Type}
namespace ExplicitCost
namespace Mirrors
theorem _root_.solution {M N : QueryMachine Q A α β} {M' N' : QueryMachine Q A α' β} {w : α → α'} {d : ℕ} (hM : Mirrors M M' w d) (hN : Mirrors N N' w d) {p : α → Bool} {p' : α' → Bool} (hp : ∀ a, p' (w a) = p a) :
    Mirrors (QueryMachine.ite p M N) (QueryMachine.ite p' M' N') w d :=
  Mirrors.branch hM hN fun a => by
    unfold Stepped.iteSel
    rw [hp a]
    cases p a <;> rfl
end Mirrors
end ExplicitCost
