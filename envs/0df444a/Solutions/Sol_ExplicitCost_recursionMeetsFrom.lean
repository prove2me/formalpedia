-- Prove2me | solution 1 for ExplicitCost.recursionMeetsFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:35:28.988324+00:00
-- url     : https://prove2.me/submissions/1590caa2-d163-462b-b369-5aeaa76ae187

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverPattern
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Meets
import Theorems.Thm_ExplicitCost_askCost_mono
import Theorems.Thm_ExplicitCost_Xi_mono
import Theorems.Thm_ExplicitCost_Xi_eq
import Theorems.Thm_ExplicitCost_room_term_le
import Theorems.Thm_ExplicitCost_lamAt_le_max
import Theorems.Thm_ExplicitCost_child_inBounds
import Theorems.Thm_ClauseBound_Gen_Pick_K_pos
import Theorems.Thm_Eight_Level_rho_ge
import Theorems.Thm_ExplicitCost_K_pos
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Run_trans
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
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Printed_AchievedBy_mono
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_mono
import Theorems.Thm_QueryMachines_QueryMachine_Runs_mono
import Theorems.Thm_QueryMachines_QueryMachine_WithinFrom_mono
import Theorems.Thm_QueryMachines_QueryMachine_Within_mono
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
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono
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
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}
namespace ExplicitCost
theorem _root_.solution : RecursionMeetsFrom := by
  intro hBase hStep hProc hChild c
  obtain ⟨C₅, h5⟩ := hBase
  obtain ⟨C₃, h3⟩ := hStep c
  obtain ⟨Cp, hp⟩ := hProc c
  refine ⟨C₅ + C₃ + Cp, fun ρ x₀ D hS l lam B _ _ => ?_⟩
  have lev : ∀ (a : Ctx) (f : TableQuery → Option Ans) (a' : Ctx), (spec D c x₀ (InBounds ρ c x₀ l lam B)).Child a f a' → ∃ j, cLev a = j + 1 := fun a _ _ h => ⟨cLev a - 1, by have := h.1; omega⟩
  refine ⟨fun a f a' hG hC => ?_, fun a f a' hG hC => ?_, fun a f a' hG hC => ?_, fun a f hG tc tq => ?_, fun a f a' hG hC q v hq tq => ?_⟩
  · obtain ⟨j, hj⟩ := lev _ _ _ hC
    have h := (hChild ρ c x₀ D hS _ a a' f j hG.2 hj hC).1
    show cLev a' + 1 = cLev a
    omega
  · obtain ⟨j, hj⟩ := lev _ _ _ hC
    obtain ⟨g1, g2, -, -, g5, g6⟩ := hChild ρ c x₀ D hS _ a a' f j hG.2 hj hC
    exact ⟨child_inBounds hS.is.rho_ge hG.1 hG.2.1 hj g1 g5 g6, g2⟩
  · obtain ⟨j, hj⟩ := lev _ _ _ hC
    obtain ⟨i1, i2, i3⟩ := hG.1
    rw [hj] at i1 i2 i3
    refine ((h3 ρ x₀ D hS _ a f j hG.2 hj).1 a' hC).trans ?_
    rw [Xi_eq]
    exact room_term_le ρ c x₀ lam B (by omega) i1 hG.2.1 i2 i3
  · obtain ⟨i1, i2, i3⟩ := hG.1
    show (solver c x₀).Within _ (solPrices c tc tq) a (solverCost (C₅ + C₃ + Cp) ρ c x₀ l lam B (cLev a) tc tq) _ _
    rcases hj : cLev a with _ | j
    · rw [hj] at i1 i2 i3
      refine (h5 D c x₀ _ _ a f hG.2 hj tc tq).mono ?_ (room_term_le (i := 0) ρ c x₀ lam B (by omega) i1 hG.2.1 i2 i3)
      have hE : 2 ^ (2 ^ x₀ * (2 ^ x₀ - 1) / 2 * cLam a) ≤ 2 ^ (2 ^ x₀ * (2 ^ x₀ - 1) / 2 * lamAt ρ c x₀ l lam B 0) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ i2)
      calc 2 ^ (2 ^ x₀ * (2 ^ x₀ - 1) / 2 * cLam a) * (2 ^ x₀ * (tq + 1) + 1) ≤ 2 ^ (2 ^ x₀ * (2 ^ x₀ - 1) / 2 * lamAt ρ c x₀ l lam B 0) * (2 ^ x₀ * (tq + 1) + 1) := Nat.mul_le_mul_right _ hE
        _ = solverCost (C₅ + C₃ + Cp) ρ c x₀ l lam B 0 tc tq := by
          simp only [solverCost, Tower.shapeS, solverOwn, solverCalls, solverAsks]
          ring
    · rw [hj] at i1 i2 i3
      have hX : Xi (Levels.Gen.g x₀ j) (cLam a) (cB a) ^ C₃ ≤ xiAt ρ c x₀ l lam B j ^ (C₅ + C₃ + Cp) := by
        have hb : 1 ≤ xiAt ρ c x₀ l lam B j := by
          have h1 := K_pos x₀ (j + 1)
          have h2 := hG.2.1
          unfold xiAt
          rw [Xi_eq]
          exact Nat.mul_pos h1 (by omega)
        exact (Nat.pow_le_pow_left (Xi_mono _ i2 i3) _).trans (Nat.pow_le_pow_right hb (by omega))
      refine ((h3 ρ x₀ D hS _ a f j hG.2 hj).2 tc tq _ (i2.trans (lamAt_le_max ρ c x₀ lam B i1))).mono ?_ ?_
      · have hI : #(D.fam (cLam a)).I ≤ (2 * lamAt ρ c x₀ l lam B (j + 1)) ^ c := (hS.is.card _ hG.2.1).trans (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ i2) _)
        have hP : #(D.fam (cLam a)).I ^ nRectG (Levels.Gen.g x₀ j) (Levels.Gen.g x₀ j) ≤ patternsAt ρ c x₀ l lam B j := Nat.pow_le_pow_left hI _
        have hA := askCost_mono c i2
        calc #(D.fam (cLam a)).I ^ nRectG (Levels.Gen.g x₀ j) (Levels.Gen.g x₀ j) * (Xi (Levels.Gen.g x₀ j) (cLam a) (cB a) ^ C₃ * Levels.Gen.K x₀ j ^ Levels.Gen.g x₀ j + tc) + (2 * #(D.fam (cLam a)).I + 2) * askCost c (cLam a) + Xi (Levels.Gen.g x₀ j) (cLam a) (cB a) ^ C₃
            ≤ patternsAt ρ c x₀ l lam B j * (xiAt ρ c x₀ l lam B j ^ (C₅ + C₃ + Cp) * Levels.Gen.K x₀ j ^ Levels.Gen.g x₀ j + tc) + (2 * (2 * lamAt ρ c x₀ l lam B (j + 1)) ^ c + 2) * askCost c (lamAt ρ c x₀ l lam B (j + 1)) + xiAt ρ c x₀ l lam B j ^ (C₅ + C₃ + Cp) :=
              Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul hP (Nat.add_le_add_right (Nat.mul_le_mul_right _ hX) _)) (Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left _ hI) _) hA)) hX
          _ = solverCost (C₅ + C₃ + Cp) ρ c x₀ l lam B (j + 1) tc tq := by
            simp only [solverCost, Tower.shapeS, solverOwn, solverCalls, solverAsks]
            ring
      · rw [Xi_eq]
        exact room_term_le ρ c x₀ lam B (by omega) i1 hG.2.1 i2 i3
  · obtain ⟨j, hj⟩ := lev _ _ _ hC
    obtain ⟨i1, i2, i3⟩ := hG.1
    rw [hj] at i1 i2 i3
    have hj' : cLev a' = j := (hChild ρ c x₀ D hS _ a a' f j hG.2 hj hC).1
    show (procedure c).Within _ (upPrices c tq) (a', q) (entryCost (C₅ + C₃ + Cp) ρ c x₀ l lam B (cLev a') tq) _ _
    rw [hj']
    have hX : Xi (Levels.Gen.g x₀ j) (cLam a) (cB a) ^ Cp ≤ xiAt ρ c x₀ l lam B j ^ (C₅ + C₃ + Cp) := by
      have hb : 1 ≤ xiAt ρ c x₀ l lam B j := by
        have h1 := K_pos x₀ (j + 1)
        have h2 := hG.2.1
        unfold xiAt
        rw [Xi_eq]
        exact Nat.mul_pos h1 (by omega)
      exact (Nat.pow_le_pow_left (Xi_mono _ i2 i3) _).trans (Nat.pow_le_pow_right hb (by omega))
    refine (hp ρ x₀ D hS _ a a' f j hG.2 hj hC q v hq tq _ (i2.trans (lamAt_le_max ρ c x₀ lam B i1))).mono ?_ ?_
    · have hA := askCost_mono c i2
      have hE : 2 ^ (Levels.Gen.g x₀ j ^ 3 * cLam a * (2 * Levels.Gen.g x₀ j / Levels.Gen.K x₀ j)) ≤ 2 ^ (Levels.Gen.g x₀ j ^ 3 * lamAt ρ c x₀ l lam B (j + 1) * (2 * Levels.Gen.g x₀ j / Levels.Gen.K x₀ j)) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ i2))
      calc 2 ^ (Levels.Gen.g x₀ j ^ 3 * cLam a * (2 * Levels.Gen.g x₀ j / Levels.Gen.K x₀ j)) * ((askCost c (cLam a) + tq) * Xi (Levels.Gen.g x₀ j) (cLam a) (cB a) ^ Cp)
          ≤ 2 ^ (Levels.Gen.g x₀ j ^ 3 * lamAt ρ c x₀ l lam B (j + 1) * (2 * Levels.Gen.g x₀ j / Levels.Gen.K x₀ j)) * ((askCost c (lamAt ρ c x₀ l lam B (j + 1)) + tq) * xiAt ρ c x₀ l lam B j ^ (C₅ + C₃ + Cp)) :=
            Nat.mul_le_mul hE (Nat.mul_le_mul (Nat.add_le_add_right hA _) hX)
        _ = entryCost (C₅ + C₃ + Cp) ρ c x₀ l lam B j tq := by
          simp only [entryCost, Tower.shapeI, entryOwn, entryAsks]
          ring
    · rw [Xi_eq]
      exact room_term_le ρ c x₀ lam B (by omega) i1 hG.2.1 i2 i3
end ExplicitCost
