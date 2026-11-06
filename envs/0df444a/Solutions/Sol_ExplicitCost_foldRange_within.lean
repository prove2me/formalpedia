-- Prove2me | solution 1 for ExplicitCost.foldRange_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:57:57.817496+00:00
-- url     : https://prove2.me/submissions/db3f8573-0ea2-4d0a-9e9a-6eeedd40841a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Answers
import Definitions.Def_QueryMachines_CombRuns
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Within
import Theorems.Thm_ExplicitCost_sum_map_flatMap_range
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_QueryMachines_stFoldRangeRuns
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines Finset
variable {Q Q' A A' α α₁ α₂ β γ : Type}
namespace ExplicitCost
theorem _root_.solution [HasSize α] [HasSize γ] {N : α → ℕ} {M : QueryMachine Q A (α × ℕ) β} {g : γ → ℕ → β → γ} {c₀ : α → γ} {O : Q → Option A} {w : Q → ℕ} {a : α} (T : ℕ → ℕ) (v : ℕ → β) (Sc Sm : ℕ)
    (hM : ∀ y < N a, M.Within O w (a, y) (T y) Sm (v y)) (hc : ∀ k ≤ N a, size ((List.range k).foldl (fun c y => g c y (v y)) (c₀ a)) ≤ Sc) :
    (QueryMachine.foldRange N M g c₀).Within O w a (∑ y ∈ range (N a), (T y + 1)) (size a + size (N a) + (Sc + Sm) + 1) ((List.range (N a)).foldl (fun c y => g c y (v y)) (c₀ a)) := by
  have h : ∀ y, ∃ (own : ℕ) (L : List Q), y < N a → M.Runs O (a, y) own L Sm (v y) ∧ own + (L.map w).sum ≤ T y := fun y => by
    by_cases hy : y < N a
    · obtain ⟨own, L, h1, h2⟩ := hM y hy
      exact ⟨own, L, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, [], fun h => absurd h hy⟩
  choose t Lq hq using h
  refine ⟨_, _, stFoldRangeRuns _ _ _ _ _ N M g c₀ O a t Lq v Sc Sm (fun y hy => (hq y hy).1) hc, ?_⟩
  rw [sum_map_flatMap_range, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun y hy => ?_
  have := (hq y (Finset.mem_range.1 hy)).2
  omega
end ExplicitCost
