-- Prove2me | solution 1 for ExplicitCost.mapAsk_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:43:26.044946+00:00
-- url     : https://prove2.me/submissions/d66041bf-683b-413c-89cc-dc01d6488922

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Answers
import Definitions.Def_QueryMachines_CombRuns
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Within
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_QueryMachines_stMapAskRuns
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines Finset
variable {Q Q' A A' α α₁ α₂ β γ : Type}
namespace ExplicitCost
theorem _root_.solution {h : Q → Q'} {M : QueryMachine Q A α β} {O : Q' → Option A} {w : Q' → ℕ} {a : α} {T S : ℕ} {b : β} (hr : M.Within (fun x => O (h x)) (fun x => w (h x)) a T S b) :
    (QueryMachine.mapAsk h M).Within O w a T S b :=
  let ⟨own, L, hr, hle⟩ := hr
  ⟨own, L.map h, stMapAskRuns _ _ _ _ _ h M O a own S L b hr, by rw [List.map_map]; exact hle⟩
end ExplicitCost
