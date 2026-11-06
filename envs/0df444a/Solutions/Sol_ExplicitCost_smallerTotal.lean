-- Prove2me | solution 1 for ExplicitCost.smallerTotal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:38:29.367705+00:00
-- url     : https://prove2.me/submissions/6d652d12-00f6-4b7c-a895-4c0611565e72

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternPsi
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_GeneralPieces_Rec_Chain
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Totals
import Theorems.Thm_ExplicitCost_capSum_piecesOf
import Theorems.Thm_ExplicitCost_totalG_lists
import Theorems.Thm_ClauseBound_Gen_Chain_total_min_le
import Theorems.Thm_ClauseBound_Gen_Rate_four_nRect_le
import Theorems.Thm_ExplicitCost_card_I_pos
import Theorems.Thm_GeneralPieces_Chain_total_eq_min
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data}
namespace ExplicitCost
theorem _root_.solution : SmallerTotal := by
  intro ρ c x₀ D hS g lam y hg hlam _
  rw [totalG_lists hS hlam, totalG_lists hS hlam, ← GeneralPieces.Chain.total_eq_min]
  have h1 : ((totalG (piecesOf D c) g g (decide (totalG (piecesOf D c) g g true 0 lam y < totalG (piecesOf D c) g g false 0 lam y)) 0 lam y : ℕ) : ℝ) ≤
      ((g * (g - 1) * g * lam + nRectG g g * capSum (piecesOf D c) 0 lam : ℕ) : ℝ) :=
    Nat.cast_le.2 (ClauseBound.Gen.Chain.total_min_le (piecesOf D c) g 0 lam y (card_I_pos hS.is hlam))
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  -- «N/g»: the straight edges
  have hs : ((g * (g - 1) * g * lam : ℕ) : ℝ) ≤ (g : ℝ) ^ 3 * lam := by
    have : g * (g - 1) * g * lam ≤ g ^ 3 * lam := by
      calc g * (g - 1) * g * lam ≤ g * g * g * lam := by gcongr; exact Nat.sub_le _ _
        _ = g ^ 3 * lam := by ring
    exact_mod_cast this
  -- «|ℛ|(4ρλ + c·log(2λ))», and |ℛ| ≤ g⁴/4
  have hcap := capSum_piecesOf hS 0 hlam
  have h0 : 0 ≤ 4 * ρ * lam + c * Real.logb 2 (2 * lam) := le_trans (Nat.cast_nonneg _) hcap
  have hR : (nRectG g g : ℝ) ≤ (g : ℝ) ^ 4 / 4 := by
    have : ((4 * nRectG g g : ℕ) : ℝ) ≤ ((g ^ 4 : ℕ) : ℝ) := by exact_mod_cast ClauseBound.Gen.Rate.four_nRect_le g
    push_cast at this
    linarith
  have h2 : (nRectG g g : ℝ) * capSum (piecesOf D c) 0 lam ≤ (g : ℝ) ^ 4 / 4 * (4 * ρ * lam + c * Real.logb 2 (2 * lam)) :=
    mul_le_mul hR hcap (Nat.cast_nonneg _) (by positivity)
  have e1 : (g : ℝ) ^ 4 * lam * (ρ + 1 / g) + (c : ℝ) / 4 * (g : ℝ) ^ 4 * Real.logb 2 (2 * lam) =
      (g : ℝ) ^ 3 * lam + (g : ℝ) ^ 4 / 4 * (4 * ρ * lam + c * Real.logb 2 (2 * lam)) := by
    field_simp
    ring
  rw [e1]
  refine h1.trans ?_
  rw [Nat.cast_add, Nat.cast_mul (nRectG g g)]
  exact add_le_add hs h2
end ExplicitCost
