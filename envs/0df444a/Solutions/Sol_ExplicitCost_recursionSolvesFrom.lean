-- Prove2me | solution 1 for ExplicitCost.recursionSolvesFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:00:44.496244+00:00
-- url     : https://prove2.me/submissions/a25a744a-e287-4cb1-9528-df5d88727818

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_EndBounds
import Definitions.Def_CountedRecursion_Within
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_EndSolves
import Theorems.Thm_ClauseBound_Gen_Rate_c_pos
import Theorems.Thm_Eight_Level_rho_ge
import Theorems.Thm_ExplicitCost_mapIn_within
import Theorems.Thm_ExplicitCost_mapOut_within
import Theorems.Thm_ExplicitCost_sizeBound_le_timeBound
import Theorems.Thm_ExplicitCost_three_timeBound_le
import Theorems.Thm_ExplicitCost_timeBound_mono


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution : RecursionSolvesFrom := by
  intro hP hRoom hRA hPoly c
  obtain ⟨C₁, h₁⟩ := hP c
  obtain ⟨C₂, h₂⟩ := hRoom c
  refine ⟨C₁ + C₂ + 1, fun ρ x₀ D Alg hA hS => ⟨(hPoly c x₀ Alg hA.polyTimeSteps).2, fun l lam B W hlam hB hW => ?_⟩⟩
  obtain ⟨T, S, ⟨own, L, hr, hle⟩, hT, hS'⟩ := h₁ ρ x₀ D Alg hA hS l lam B W hlam hB hW
  have hroom := h₂ ρ x₀ l lam B hS.is.rho_ge hS.is.rho_lt hS.is.c_pos hS.x₀_ge hS.x₀_c hlam hB
  -- the answers are integers
  have r1 : (readAs Sum.inl (recursionWith c x₀ Alg)).Within (tables (Levels.Gen.K x₀ l) lam W) QueryMachine.unitCost (top l lam B) T S (.inl (clique (Levels.Gen.K x₀ l) lam fun w => W w.val).value) :=
    ⟨own, L, hRA _ _ _ _ _ Sum.inl _ (answersOf (Levels.Gen.K x₀ l) lam W) (tables (Levels.Gen.K x₀ l) lam W) _ own S L _ (fun _ => rfl) hr, hle⟩
  -- the input is (ℓ, λ, B), the result an integer
  have r2 : (cliqueMachine c x₀ Alg).Within (tables (Levels.Gen.K x₀ l) lam W) QueryMachine.unitCost (unary l, unary lam, unary B) T S (clique (Levels.Gen.K x₀ l) lam fun w => W w.val).value :=
    mapOut_within (g := asInt) (mapIn_within (g := fun h : Head => ((h, none) : Ctx)) (a := (unary l, unary lam, unary B)) r1)
  have m1 := timeBound_mono ρ hS.x₀_ge l hlam hB (Nat.le_add_right C₁ C₂)
  have m2 := timeBound_mono ρ hS.x₀_ge l hlam hB (Nat.le_add_left C₂ C₁)
  have m3 := three_timeBound_le ρ hS.x₀_ge l hlam hB (C₁ + C₂)
  have m4 := sizeBound_le_timeBound hS.is.rho_ge hS.x₀_ge l hlam hB C₁
  refine ⟨T, S, r2, ?_, ?_⟩
  · change (T : ℝ) ≤ timeBound ρ x₀ (C₁ + C₂ + 1) l lam B
    linarith
  · change (S : ℝ) ≤ timeBound ρ x₀ (C₁ + C₂ + 1) l lam B
    linarith
end ExplicitCost
