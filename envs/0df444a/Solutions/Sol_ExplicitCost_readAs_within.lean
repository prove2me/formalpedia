-- Prove2me | solution 1 for ExplicitCost.readAs_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:43:37.160195+00:00
-- url     : https://prove2.me/submissions/1d087d5d-6659-4b27-ad70-fcecd1904d25

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Answers
import Definitions.Def_QueryMachines_CombRuns
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Within
import Theorems.Thm_ExplicitCost_readAs_reaches
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines Finset
variable {Q Q' A A' α α₁ α₂ β γ : Type}
namespace ExplicitCost
theorem _root_.solution {r : A' → A} {M : QueryMachine Q A α β} {O : Q → Option A} {O' : Q → Option A'} (h : ∀ x, (O' x).map r = O x) {w : Q → ℕ} {a : α} {T S : ℕ} {b : β}
    (hr : M.Within O w a T S b) : (readAs r M).Within O' w a T S b :=
  let ⟨own, L, hr, hle⟩ := hr
  ⟨own, L, readAs_reaches h hr, hle⟩
end ExplicitCost
