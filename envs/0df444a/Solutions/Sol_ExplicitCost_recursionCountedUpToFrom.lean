-- Prove2me | solution 1 for ExplicitCost.recursionCountedUpToFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:32:36.21468+00:00
-- url     : https://prove2.me/submissions/c9fd900d-bec7-4141-ab0a-3a9b4c1fe8a9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_EndBounds
import Definitions.Def_CountedRecursion_CliqueReads
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_EndCounted
import Theorems.Thm_ExplicitCost_cLev_top
import Theorems.Thm_ExplicitCost_cLam_top
import Theorems.Thm_ExplicitCost_top_inBounds
import Theorems.Thm_ExplicitCost_top_fits
import Theorems.Thm_ClauseBound_Gen_Rate_c_pos
import Theorems.Thm_Eight_Level_rho_ge
import Theorems.Thm_ExplicitCost_clique_readTables
import Theorems.Thm_ExplicitCost_sizeBound_mono
import Theorems.Thm_ExplicitCost_timeBound_mono
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution : RecursionCountedUpToFrom := by
  intro hM hT hR hTR c
  obtain ⟨C, hC⟩ := hM c
  obtain ⟨C₁, hC₁⟩ := hT c C
  obtain ⟨C₂, hC₂⟩ := hR c C
  refine ⟨max C₁ C₂, fun ρ x₀ D hS l lam B W hlam hB hW => ?_⟩
  have run : (recursion c x₀).Within (Sum.elim (answersOf (Levels.Gen.K x₀ l) lam W) (piecesUpTo D (lamMax ρ c x₀ l lam B))) (upPrices c 1) (top l lam B)
      (Tower.cost (solverCost C ρ c x₀ l lam B) (entryCost C ρ c x₀ l lam B) (cLev (top l lam B)) 1)
      (Tower.towerSize (cLev (top l lam B)) (roomAll C ρ c x₀ l lam B) (roomAll C ρ c x₀ l lam B) (roomAll C ρ c x₀ l lam B))
      (.inl (clique (Levels.Gen.K x₀ (cLev (top l lam B))) (cLam (top l lam B)) fun w => readTables (answersOf (Levels.Gen.K x₀ l) lam W) w.val).value) :=
    hTR Ctx TableQuery PieceQuery Ans (spec D c x₀ (InBounds ρ c x₀ l lam B)) _ _ _ _ _ _ _ _ _ (hC ρ x₀ D hS l lam B hlam hB) (top l lam B) (answersOf (Levels.Gen.K x₀ l) lam W)
      ⟨top_inBounds ρ c x₀ l lam B, top_fits x₀ l hlam hB hW⟩ 1
  rw [cLev_top, cLam_top, clique_readTables] at run
  exact ⟨_, _, run,
    (hC₁ ρ x₀ l lam B hS.is.rho_ge hS.is.rho_lt hS.is.c_pos hS.x₀_ge hS.x₀_c hlam hB).trans (timeBound_mono ρ hS.x₀_ge l hlam hB (le_max_left _ _)),
    (hC₂ ρ x₀ l lam B hS.is.rho_ge hS.is.rho_lt hS.is.c_pos hS.x₀_ge hS.x₀_c hlam hB).trans (sizeBound_mono hS.x₀_ge l hlam hB (le_max_right _ _))⟩
end ExplicitCost
