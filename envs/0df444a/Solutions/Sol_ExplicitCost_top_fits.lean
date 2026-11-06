-- Prove2me | solution 1 for ExplicitCost.top_fits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:21:51.034735+00:00
-- url     : https://prove2.me/submissions/ceeee503-e26f-4376-9bfc-3851f09b87a2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_EndBounds
import Definitions.Def_CountedRecursion_CliqueReads
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_EndCounted
import Theorems.Thm_ExplicitCost_cLev_top
import Theorems.Thm_ExplicitCost_cLam_top
import Theorems.Thm_ExplicitCost_cB_top

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (x₀ l : ℕ) {lam B : ℕ} (hlam : 1 ≤ lam) (hB : 1 ≤ B) {W : ℕ → List Bool → ℤ} (hW : ∀ w < Levels.Gen.K x₀ l, ∀ z ∈ words ((Levels.Gen.K x₀ l - 1) * lam), |W w z| < 2 ^ B) :
    Fits x₀ (top l lam B) (answersOf (Levels.Gen.K x₀ l) lam W) := by
  unfold Fits
  rw [cLev_top, cLam_top, cB_top]
  exact ⟨hlam, hB, W, hW, rfl⟩
end ExplicitCost
