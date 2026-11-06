-- Prove2me | solution 1 for ExplicitCost.caseTwoApplies
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:38:45.2339+00:00
-- url     : https://prove2.me/submissions/5cf05aa5-7938-46ba-a94c-a88a22971ec6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternPsi
import Definitions.Def_GeneralPieces_Rec_Chain
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CaseTwo
import Theorems.Thm_ExplicitCost_zeta_cast
import Theorems.Thm_ExplicitCost_shared_le
import Theorems.Thm_ClauseBound_Gen_Pick_K_le_g
import Theorems.Thm_ClauseBound_Gen_Rate_K_le_g
import Theorems.Thm_ClauseBound_Gen_Rate_big_le_K
import Theorems.Thm_ExplicitCost_nParts_self
import Theorems.Thm_GeneralPieces_Chain_K_dvd_g
import Theorems.Thm_GeneralPieces_Chain_hoeffding_cond
import Theorems.Thm_SingleBitPieces_Level_Presents_nParts_self


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution : CaseTwoApplies := by
  intro ρ c x₀ D hS l lam y tr W hlam _
  have e : ((nParts (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) tr : ℕ) : ℝ) = (Levels.Gen.g x₀ l : ℝ) := by rw [nParts_self]
  have hg0 : (0 : ℝ) < Levels.Gen.g x₀ l := by
    have h1 := ClauseBound.Gen.Rate.big_le_K hS.x₀_ge l
    have h2 := ClauseBound.Gen.Rate.K_le_g x₀ l
    exact_mod_cast (by omega : 0 < Levels.Gen.g x₀ l)
  refine Or.inr ⟨?_, fun a b _ => ?_, ?_⟩
  · -- «K divides g»
    rw [nParts_self]
    exact GeneralPieces.Chain.K_dvd_g x₀ l
  · -- «c_{a,a'} ≤ g²λ = P/g»
    rw [e, le_div_iff₀ hg0]
    have h : (patternNet D c (Levels.Gen.g x₀ l) tr lam y W).c a b * Levels.Gen.g x₀ l ≤ Levels.Gen.g x₀ l ^ 3 * lam := by
      calc _ ≤ Levels.Gen.g x₀ l ^ 2 * lam * Levels.Gen.g x₀ l := Nat.mul_le_mul_right _ (shared_le hS _ hlam y tr W a b)
        _ = Levels.Gen.g x₀ l ^ 3 * lam := by ring
    exact_mod_cast h
  · -- 2ζ²g ≥ K·ln(2gK)
    rw [e, zeta_cast]
    exact GeneralPieces.Chain.hoeffding_cond x₀ l hS.x₀_ge
end ExplicitCost
