-- Prove2me | solution 1 for ExplicitCost.totalCountFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:58:39.735512+00:00
-- url     : https://prove2.me/submissions/bbd6fdda-047c-42b6-ac14-0f0fb694a331

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CountBase
import Definitions.Def_CountedRecursion_CountStep
import Definitions.Def_Tower_Cost
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_TotalCount
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_key
import Theorems.Thm_ExplicitCost_bitsAt_self
import Theorems.Thm_ExplicitCost_four_mul_le_xiAt
import Theorems.Thm_ExplicitCost_lamAt_self
import Theorems.Thm_ExplicitCost_levelBound_succ
import Theorems.Thm_ExplicitCost_one_le_bitsAt
import Theorems.Thm_GeneralPieces_Trim_length_bitsOf
import Theorems.Thm_GeneralPieces_Trim_length_rep
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_TM_beq_LR
import Theorems.Thm_Groundwork_TM_beq_RL
import Theorems.Thm_Groundwork_TM_beq_bL
import Theorems.Thm_Groundwork_TM_beq_bR
import Theorems.Thm_Groundwork_TM_length_mirror
import Theorems.Thm_Groundwork_TM_st4_cnt
import Theorems.Thm_Groundwork_TM_st4_src
import Theorems.Thm_Groundwork_TM_st4_t1
import Theorems.Thm_Groundwork_TM_st4_t2
import Theorems.Thm_Groundwork_TM_st_a
import Theorems.Thm_Groundwork_TM_st_b
import Theorems.Thm_Groundwork_TM_st_cnt
import Theorems.Thm_Groundwork_TM_st_main
import Theorems.Thm_Groundwork_TM_upd4_cnt
import Theorems.Thm_Groundwork_TM_upd4_src
import Theorems.Thm_Groundwork_TM_upd4_t1
import Theorems.Thm_Groundwork_TM_upd4_t2
import Theorems.Thm_Groundwork_TM_upd_a
import Theorems.Thm_Groundwork_TM_upd_b
import Theorems.Thm_Groundwork_TM_upd_main
import Theorems.Thm_Groundwork_TM_update_withIO
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_unit
import Theorems.Thm_QueryMachines_QueryMachine_close_bind
import Theorems.Thm_QueryMachines_QueryMachine_close_both
import Theorems.Thm_QueryMachines_QueryMachine_close_branch
import Theorems.Thm_QueryMachines_QueryMachine_close_const
import Theorems.Thm_QueryMachines_QueryMachine_close_foldRange
import Theorems.Thm_QueryMachines_QueryMachine_close_foldWhile
import Theorems.Thm_QueryMachines_QueryMachine_close_gated
import Theorems.Thm_QueryMachines_QueryMachine_close_ite
import Theorems.Thm_QueryMachines_QueryMachine_close_lift
import Theorems.Thm_QueryMachines_QueryMachine_close_mapAsk
import Theorems.Thm_QueryMachines_QueryMachine_close_mapIn
import Theorems.Thm_QueryMachines_QueryMachine_close_mapOut
import Theorems.Thm_QueryMachines_QueryMachine_close_optBind
import Theorems.Thm_QueryMachines_QueryMachine_close_prodRange
import Theorems.Thm_QueryMachines_QueryMachine_close_query
import Theorems.Thm_QueryMachines_QueryMachine_close_subst
import Theorems.Thm_QueryMachines_QueryMachine_close_sumRange
attribute [local simp] GeneralPieces.Trim.length_bitsOf
attribute [local simp] GeneralPieces.Trim.length_rep
attribute [local simp] Groundwork.Host.upd_none
attribute [local simp] Groundwork.Host.withIO_none
attribute [local simp] Groundwork.Host.withIO_some
attribute [local simp] Groundwork.TM.beq_LR
attribute [local simp] Groundwork.TM.beq_RL
attribute [local simp] Groundwork.TM.beq_bL
attribute [local simp] Groundwork.TM.beq_bR
attribute [local simp] Groundwork.TM.length_mirror
attribute [local simp] Groundwork.TM.st4_cnt
attribute [local simp] Groundwork.TM.st4_src
attribute [local simp] Groundwork.TM.st4_t1
attribute [local simp] Groundwork.TM.st4_t2
attribute [local simp] Groundwork.TM.st_a
attribute [local simp] Groundwork.TM.st_b
attribute [local simp] Groundwork.TM.st_cnt
attribute [local simp] Groundwork.TM.st_main
attribute [local simp] Groundwork.TM.upd4_cnt
attribute [local simp] Groundwork.TM.upd4_src
attribute [local simp] Groundwork.TM.upd4_t1
attribute [local simp] Groundwork.TM.upd4_t2
attribute [local simp] Groundwork.TM.upd_a
attribute [local simp] Groundwork.TM.upd_b
attribute [local simp] Groundwork.TM.upd_main
attribute [local simp] Groundwork.TM.update_withIO
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_unit
attribute [local simp] QueryMachines.QueryMachine.close_bind
attribute [local simp] QueryMachines.QueryMachine.close_both
attribute [local simp] QueryMachines.QueryMachine.close_branch
attribute [local simp] QueryMachines.QueryMachine.close_const
attribute [local simp] QueryMachines.QueryMachine.close_foldRange
attribute [local simp] QueryMachines.QueryMachine.close_foldWhile
attribute [local simp] QueryMachines.QueryMachine.close_gated
attribute [local simp] QueryMachines.QueryMachine.close_ite
attribute [local simp] QueryMachines.QueryMachine.close_lift
attribute [local simp] QueryMachines.QueryMachine.close_mapAsk
attribute [local simp] QueryMachines.QueryMachine.close_mapIn
attribute [local simp] QueryMachines.QueryMachine.close_mapOut
attribute [local simp] QueryMachines.QueryMachine.close_optBind
attribute [local simp] QueryMachines.QueryMachine.close_prodRange
attribute [local simp] QueryMachines.QueryMachine.close_query
attribute [local simp] QueryMachines.QueryMachine.close_subst
attribute [local simp] QueryMachines.QueryMachine.close_sumRange



set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed QueryMachines
namespace ExplicitCost
theorem _root_.solution : TotalCountFrom := by
  intro hB hS hF hShape c C
  obtain ⟨C₄, hC₄⟩ := hS c C
  refine ⟨2 * (c + C₄ + 1), fun ρ x₀ l lam B h1 h2 h3 h4 h5 h6 h7 => ?_⟩
  have hN : Numbers ρ c x₀ lam B := ⟨h1, h2, h3, h4, h5, h6, h7⟩
  have key : ∀ j, j ≤ l → ∀ t, 1 ≤ t →
      (Tower.cost (solverCost C ρ c x₀ l lam B) (entryCost C ρ c x₀ l lam B) j t : ℝ) ≤ t * levelBound ρ c x₀ (2 * (c + C₄ + 1)) l lam B j := by
    intro j
    induction j with
    | zero =>
      intro _ t ht
      exact hB C ρ c x₀ _ l lam B t hN (by omega) ht
    | succ j ih =>
      intro hj t ht
      have eq1 : Tower.cost (solverCost C ρ c x₀ l lam B) (entryCost C ρ c x₀ l lam B) (j + 1) t =
          solverOwn C ρ c x₀ l lam B (j + 1) + solverCalls ρ c x₀ l lam B (j + 1) *
            (Tower.cost (solverCost C ρ c x₀ l lam B) (entryCost C ρ c x₀ l lam B) j (entryCost C ρ c x₀ l lam B j t + 2) + 2) + 0 * t :=
        hShape (solverOwn C ρ c x₀ l lam B) (solverCalls ρ c x₀ l lam B) (solverAsks ρ c x₀ l lam B) (entryOwn C ρ c x₀ l lam B) (entryAsks C ρ c x₀ l lam B) j t
      have ih' := ih (by omega) (entryCost C ρ c x₀ l lam B j t + 2) (by omega)
      have hs := hC₄ ρ x₀ (2 * (c + C₄ + 1)) l lam B j t hN (by omega) ht
      have hx1 : 1 ≤ x₀ := by omega
      have hXn := four_mul_le_xiAt hx1 ρ c l lam B j (one_le_bitsAt hN hj)
      have hX1 : (1 : ℝ) ≤ (xiAt ρ c x₀ l lam B j : ℝ) := by exact_mod_cast (by omega : 1 ≤ xiAt ρ c x₀ l lam B j)
      have hf := hF c C₄ (2 * (c + C₄ + 1)) x₀ j h4 h5 le_rfl
      rw [eq1]
      push_cast at ih' ⊢
      have a1 : (solverCalls ρ c x₀ l lam B (j + 1) : ℝ) * ((Tower.cost (solverCost C ρ c x₀ l lam B) (entryCost C ρ c x₀ l lam B) j (entryCost C ρ c x₀ l lam B j t + 2) : ℝ) + 2) ≤
          (solverCalls ρ c x₀ l lam B (j + 1) : ℝ) * (((entryCost C ρ c x₀ l lam B j t : ℝ) + 2) * levelBound ρ c x₀ (2 * (c + C₄ + 1)) l lam B j + 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
      have a2 : (t : ℝ) * ((2 : ℝ) ^ (e ρ x₀ (j + 1) * (K x₀ (j + 1) : ℝ) ^ 2 * lamAt ρ c x₀ l lam B (j + 1)) *
          (xiAt ρ c x₀ l lam B j : ℝ) ^ (c * g x₀ j ^ 4 / 2 + g x₀ j + K x₀ j ^ 2 + C₄ + (c + 5) * (2 * (c + C₄ + 1)) * K x₀ j ^ 2)) ≤ t * levelBound ρ c x₀ (2 * (c + C₄ + 1)) l lam B (j + 1) := by
        rw [levelBound_succ]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX1 hf) (by positivity)) (Nat.cast_nonneg _)
      linarith
  have h := key l le_rfl 1 le_rfl
  unfold levelBound at h
  rw [lamAt_self, bitsAt_self] at h
  simpa using h
end ExplicitCost
