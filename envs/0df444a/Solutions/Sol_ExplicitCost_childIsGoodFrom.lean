-- Prove2me | solution 1 for ExplicitCost.childIsGoodFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:47:09.538191+00:00
-- url     : https://prove2.me/submissions/1bd4e9c3-344d-4cda-9f98-23ecf04486cb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CallFacts
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_ChildIsGood
import Theorems.Thm_ExplicitCost_callNet_total_le
import Theorems.Thm_Eight_Level_rho_ge
import Theorems.Thm_Eight_SecNetworks_L_le
import Theorems.Thm_ExplicitCost_at_call
import Theorems.Thm_ExplicitCost_child_value
import Theorems.Thm_ExplicitCost_entryCost_cast
import Theorems.Thm_ExplicitCost_fits_succ
import Theorems.Thm_ExplicitCost_groupClique_value
import Theorems.Thm_ExplicitCost_groupTables_mkParent
import Theorems.Thm_ExplicitCost_length_unary
import Theorems.Thm_ExplicitCost_level_numbers
import Theorems.Thm_ExplicitCost_nParts_self
import Theorems.Thm_ExplicitCost_nPatterns_readyOf
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Printed_length_unary
import Theorems.Thm_SingleBitPieces_Level_Presents_nParts_self


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution : ChildIsGoodFrom := by
  intro hG hL hE hV hBN hT hSm hC hLB ρ c x₀ D hS Bound a a' f l hF hl hc
  obtain ⟨y, x, h⟩ := at_call hG hL hC hBN hS hF hl hc
  obtain ⟨c₁, hE⟩ := entryCost_cast hE
  obtain ⟨hK2, hKg, hg2⟩ := level_numbers hS.x₀_ge l
  obtain ⟨hlam, -, -, -⟩ := fits_succ hF hl
  have hK0 : 0 < Levels.Gen.K x₀ l := by omega
  have hpY : pY (parentOf a') = y := by rw [h.parent]; rfl
  have hpK : pK (parentOf a') = Levels.Gen.K x₀ (cLev a') := by
    rw [h.parent, h.lev]
    exact length_unary _
  refine ⟨h.lev, ⟨?_, ?_, groupTables D c (parentOf a') (cLam a') (readTables f), ?_, ?_⟩, ?_, ?_, ?_, h.bits⟩
  · rw [h.lam]
    exact h.L_pos
  · rw [h.bits]
    exact (Nat.mul_pos (Nat.pow_pos (by omega)) h.is.B_pos).trans_le (Nat.le_add_left _ _)
  · intro w hw z hz
    rw [h.lev] at hw hz
    rw [h.lam] at hz
    rw [h.parent, h.lam, h.bits]
    unfold callParent
    rw [groupTables_mkParent]
    beta_reduce
    rw [dif_pos hw]
    exact (hE _ _ _ (nParts_self _ _) _ (callNet D c x₀ l a f y) _ _ 1 hKg h.is le_rfl x h.x_lt _ (h.L_le.trans (Nat.le_mul_of_pos_left _ (by norm_num))) (h.few _) (h.short _) ⟨w, hw⟩ z hz).2
  · change answersOf (pK (parentOf a')) (cLam a') _ = _
    rw [hpK]
  · rw [hpY, nPatterns_readyOf D x₀ a.1 hl]
    exact h.y_lt
  · rw [hpY, child_value D c x₀ Bound a' f (congrArg (Levels.Gen.K x₀) h.lev) h.parent h.lam hK0]
    exact congrArg Sum.inl (groupClique_value hV hK0 (callNet D c x₀ l a f y) h.is x _ (h.short hK0))
  · rw [h.lam]
    exact hLB ρ c x₀ l (cLam a) _ hS.is.rho_ge hS.x₀_ge hlam (callNet_total_le hT hSm hS f hl hlam h.y_lt)
end ExplicitCost
