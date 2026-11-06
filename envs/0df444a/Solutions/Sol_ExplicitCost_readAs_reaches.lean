-- Prove2me | solution 1 for ExplicitCost.readAs_reaches
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:52:01.335762+00:00
-- url     : https://prove2.me/submissions/bb220075-aa97-4f2d-859c-da02a213a6dd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_AnswersDefs
import Definitions.Def_QueryMachines_Runs
import Definitions.Def_QueryMachines_Poly
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Answers
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines Printed
variable {Q A A' α β : Type}
namespace ExplicitCost
theorem _root_.solution {r : A' → A} {M : QueryMachine Q A α β} {O : Q → Option A} {O' : Q → Option A'} (h : ∀ x, (O' x).map r = O x) {S own : ℕ} {L : List Q} {b : β} {s : M.σ}
    (hr : M.Reaches O S b s own L) : (readAs r M).Reaches O' S b s own L := by
  induction hr with
  | halt ho hs => exact .halt ho hs
  | step ho ha hs _ ih => exact .step ho ha hs ih
  | @query s own L x v ho ha hv hs _ ih =>
    obtain ⟨v', hv', rfl⟩ : ∃ v', O' x = some v' ∧ r v' = v := by
      have e := h x
      rw [hv] at e
      exact Option.map_eq_some_iff.1 e
    exact .query ho ha hv' hs ih
end ExplicitCost
