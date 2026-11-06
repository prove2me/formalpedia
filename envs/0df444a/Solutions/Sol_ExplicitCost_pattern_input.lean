-- Prove2me | solution 1 for ExplicitCost.pattern_input
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:17:52.759016+00:00
-- url     : https://prove2.me/submissions/6680ddb2-455b-4eb3-a356-399db32724e2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CliqueReads
import Definitions.Def_CountedRecursion_SolverStages
import Definitions.Def_CountedRecursion_LevelNumbers
import Definitions.Def_Printed_GroupingEntry
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverPattern
import Theorems.Thm_ExplicitCost_two_le_K
import Theorems.Thm_ExplicitCost_nPatterns_ready
import Theorems.Thm_ExplicitCost_tables_lt
import Theorems.Thm_ExplicitCost_lof_le
import Theorems.Thm_ExplicitCost_total_le_gP
import Theorems.Thm_ClauseBound_Gen_Pick_K_le_g
import Theorems.Thm_ExplicitCost_K_le_g
import Theorems.Thm_ExplicitCost_nParts_self
import Theorems.Thm_ExplicitCost_parentAt_readyOf
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
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
import Theorems.Thm_SingleBitPieces_Level_Presents_nParts_self
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
variable {ρ : ℝ} {c x₀ l y : ℕ} {D : PiecesCounted.Data} {a : Ctx} {f : TableQuery → Option Ans}
namespace ExplicitCost
theorem _root_.solution (hLL : LabelLengthIsL) (hBN : BothNetworks) (hS : Setting ρ c x₀ D) (hF : Fits x₀ a f) (hl : cLev a = l + 1) (hy : y < nPatterns (readyOf D x₀ a.1)) :
    (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).Is (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) ∧
    searchInput c (readyOf D x₀ a.1, y) = groupingInput 1 (2 ^ (l + 5)) (Levels.Gen.K x₀ l) (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) ∧
    labelLength (searchInput c (readyOf D x₀ a.1, y)) = AppRunningTime.Lof (Levels.Gen.K x₀ l) (nParts (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y))) (((1 : ℕ) : ℝ) / ((2 ^ (l + 5) : ℕ) : ℝ)) (Levels.Gen.g x₀ l ^ 3 * cLam a) (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).U ∧
    labelLength (searchInput c (readyOf D x₀ a.1, y)) ≤ 3 * (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a)) := by
  obtain ⟨C₂, hC₂⟩ := hBN c
  have hK2 := two_le_K (by have := hS.x₀_ge; omega : 1 ≤ x₀) l
  have hKg := K_le_g x₀ l
  rw [nPatterns_ready D x₀ a.1 hl] at hy
  obtain ⟨hIs, -, hin, -⟩ := hC₂ ρ x₀ D hS (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (cLam a) (cB a) y 0 0 (cLam a) (direction (readyOf D x₀ a.1, y)) (readTables f) (by omega) hKg hF.1 le_rfl hF.2.1 (tables_lt hF hl) hy (by positivity)
  have e : unary (nParts (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y))) = unary (Levels.Gen.g x₀ l) := by rw [nParts_self]
  have hsi : searchInput c (readyOf D x₀ a.1, y) = groupingInput 1 (2 ^ (l + 5)) (Levels.Gen.K x₀ l) (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) := by
    simp only [searchInput, groupingInput, dataInput, e]
    rw [parentAt_readyOf D x₀ a.1 hl y 0]
    refine Prod.ext (Prod.ext rfl ?_) hin
    show 2 ^ (cLev a + 4) = 2 ^ (l + 5)
    rw [hl]
  have hL := (hLL 1 (2 ^ (l + 5)) (Levels.Gen.K x₀ l) _ (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) (by positivity) (Nat.one_le_two_pow) (by omega) hIs).1
  refine ⟨hIs, hsi, by rw [hsi]; exact hL, ?_⟩
  rw [hsi, hL]
  have h := lof_le (K := Levels.Gen.K x₀ l) (g := nParts (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y))) (P := (Levels.Gen.g x₀ l ^ 3 * cLam a)) (U := (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).U) (ζ := ((1 : ℕ) : ℝ) / ((2 ^ (l + 5) : ℕ) : ℝ)) (by omega) (by positivity)
    ((div_le_one (by positivity)).2 (by exact_mod_cast Nat.one_le_two_pow)) (total_le_gP hIs)
  exact h.trans (le_of_eq (by rw [nParts_self]))
end ExplicitCost
