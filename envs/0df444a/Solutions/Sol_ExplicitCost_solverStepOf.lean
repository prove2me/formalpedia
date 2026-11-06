-- Prove2me | solution 1 for ExplicitCost.solverStepOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:12:27.676195+00:00
-- url     : https://prove2.me/submissions/c634dc88-4854-489e-9fc5-842a6f0f6d45

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverRoom
import Definitions.Def_CountedRecursion_GridLemmas
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverStep
import Theorems.Thm_ExplicitCost_pieces_ask
import Theorems.Thm_ExplicitCost_pieces_cap
import Theorems.Thm_ExplicitCost_division_exact
import Theorems.Thm_ClauseBound_Gen_Pick_K_pos
import Theorems.Thm_ExplicitCost_K_pos
import Theorems.Thm_ExplicitCost_child_size
import Theorems.Thm_ExplicitCost_ite_within_false
import Theorems.Thm_ExplicitCost_levelSolver_within
import Theorems.Thm_ExplicitCost_mapIn_within
import Theorems.Thm_ExplicitCost_mapOut_within
import Theorems.Thm_ExplicitCost_nPatterns_ready
import Theorems.Thm_ExplicitCost_pattern_run
import Theorems.Thm_ExplicitCost_solver_room
import Theorems.Thm_ExplicitCost_sumAndDivide_within
import Theorems.Thm_ExplicitCost_unary_length_eq
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_length
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
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.length
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
variable {ρ : ℝ} {c x₀ l : ℕ} {D : PiecesCounted.Data} {a : Ctx} {f : TableQuery → Option Ans}
namespace ExplicitCost
theorem _root_.solution : NumbersRun → Expansion → PatternsFew → GroupingWithCall → LabelLengthIsL → ValueIsKept → BothNetworks → CaseTwoApplies → CrudeBounds → QueryMachines.StSubstWithin → SolverStep := by
  intro hNum hExp hFew hGW hLL hV hBN hC2 hCr hSub c
  obtain ⟨Cn, hCn⟩ := hNum
  obtain ⟨Cg, hCg⟩ := pattern_run hGW hLL hV hBN hC2 hSub c
  obtain ⟨C, hC⟩ := solver_room hFew hCr c Cn Cg
  refine ⟨C, fun ρ x₀ D hS Bound a f l hF hl => ?_⟩
  obtain ⟨hroom, hc1, hc2⟩ := hC ρ x₀ D hS a l hF.1 hF.2.1 hl
  refine ⟨fun a' hCh => (child_size hLL hBN hS Bound hF hl a' hCh).trans (le_trans (by omega) hroom), fun tc tq Lam hLam => ?_⟩
  have hpat := hCg ρ x₀ D hS Bound a f l hF hl
  have h6 := sumAndDivide_within (c := c) (O := ((spec D c x₀ Bound).oracle (piecesUpTo D Lam) a f)) (w := solPrices c tc tq) (r := readyOf D x₀ a.1) (Cg * Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l + (tc + 2)) ((Levels.Gen.g x₀ l * ((Levels.Gen.g x₀ l ^ 3 * cLam a) + (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) + size ((1 : ℕ), 2 ^ (l + 5))) ^ Cg + (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) + Levels.Gen.g x₀ l * Levels.Gen.g x₀ l * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) + 2 * (2 * size (readyOf D x₀ a.1) + 2 * size (nPatterns (readyOf D x₀ a.1)) + size (Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l) + 2 * Levels.Gen.g x₀ l + 6 * (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a)) + 2 * bitsOut (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) + 12)) (2 ^ (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) + Levels.Gen.g x₀ l * Levels.Gen.g x₀ l * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))))
    (fun y => (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).value) (fun y hy => (hpat y hy).2 tc tq Lam) (fun y hy => (hpat y hy).1)
  have s5 : hLev a.1 - 1 = l := by
    have : hLev a.1 = l + 1 := hl
    omega
  have ht : a.1.1.tail = unary l := by
    rw [← unary_length_eq a.1.1.tail, List.length_tail]
    show unary (hLev a.1 - 1) = _
    rw [s5]
  have hN : (numbersM x₀).Runs a.1.1.tail (2 * l) (Cn * Levels.Gen.g x₀ l) (unary (2 ^ (3 * (hLev a.1 - 1) + x₀)), unary (Levels.Gen.K x₀ (hLev a.1 - 1))) := by
    rw [ht, s5]
    exact hCn x₀ l
  have hu1 : 1 ≤ a.1.2.1.length := hF.1
  have hu2 : a.1.2.1.length ≤ Lam := hLam
  have hlev : (levelSolver c x₀).Within ((spec D c x₀ Bound).oracle (piecesUpTo D Lam) a f) (solPrices c tc tq) a.1 (2 * l + 5 + 2 * #(D.fam (cLam a)).I + (2 * #(D.fam (cLam a)).I + 2) * askCost c (cLam a) + (nPatterns (readyOf D x₀ a.1) * (Cg * Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l + (tc + 2) + 1) + 2)) (Cn * Levels.Gen.g x₀ l + 8 * size (readyOf D x₀ a.1) + (2 * size (readyOf D x₀ a.1) + size (nPatterns (readyOf D x₀ a.1)) + size (nPatterns (readyOf D x₀ a.1) * 2 ^ (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) + Levels.Gen.g x₀ l * Levels.Gen.g x₀ l * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)))) + ((Levels.Gen.g x₀ l * ((Levels.Gen.g x₀ l ^ 3 * cLam a) + (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) + size ((1 : ℕ), 2 ^ (l + 5))) ^ Cg + (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) + Levels.Gen.g x₀ l * Levels.Gen.g x₀ l * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) + 2 * (2 * size (readyOf D x₀ a.1) + 2 * size (nPatterns (readyOf D x₀ a.1)) + size (Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l) + 2 * Levels.Gen.g x₀ l + 6 * (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a)) + 2 * bitsOut (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) + 12)) + 3) + 10) ((∑ y ∈ range (nPatterns (readyOf D x₀ a.1)), (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).value) / (((rD (readyOf D x₀ a.1)).toNat ^ rRect (readyOf D x₀ a.1) : ℕ) : ℤ)) := by
    have hor : ∀ q, ((spec D c x₀ Bound).oracle (piecesUpTo D Lam) a f) (Sum.inr (Sum.inr (a.1.2.1, q))) = D.answer (cLam a) q := fun q => pieces_ask D hu1 hu2 q
    have hI : ((spec D c x₀ Bound).oracle (piecesUpTo D Lam) a f) (Sum.inr (Sum.inr (a.1.2.1, .inr (.inl ())))) = some (.inr (listsOf D (cLam a)).1) := hor _
    have hd : ((spec D c x₀ Bound).oracle (piecesUpTo D Lam) a f) (Sum.inr (Sum.inr (a.1.2.1, .inl ()))) = some (.inl (D.fam (cLam a)).d) := hor _
    have h₀ : ∀ j < (listsOf D (cLam a)).1.length, ((spec D c x₀ Bound).oracle (piecesUpTo D Lam) a f) (Sum.inr (Sum.inr (a.1.2.1, .inr (.inr (.inl (false, (listsOf D (cLam a)).1.getD j 0)))))) = some (.inl (((listsOf D (cLam a)).2.1.getD j 0 : ℕ) : ℤ)) :=
      fun j hj => (hor _).trans (pieces_cap D (cLam a) false hj)
    have h₁ : ∀ j < (listsOf D (cLam a)).1.length, ((spec D c x₀ Bound).oracle (piecesUpTo D Lam) a f) (Sum.inr (Sum.inr (a.1.2.1, .inr (.inr (.inl (true, (listsOf D (cLam a)).1.getD j 0)))))) = some (.inl (((listsOf D (cLam a)).2.2.getD j 0 : ℕ) : ℤ)) :=
      fun j hj => (hor _).trans (pieces_cap D (cLam a) true hj)
    have hl₀ : (listsOf D (cLam a)).2.1.length = (listsOf D (cLam a)).1.length := List.length_map _
    have hl₁ : (listsOf D (cLam a)).2.2.length = (listsOf D (cLam a)).1.length := List.length_map _
    have hlen : (listsOf D (cLam a)).1.length = #(D.fam (cLam a)).I := Finset.length_sort _
    have h := levelSolver_within (c := c) (O := ((spec D c x₀ Bound).oracle (piecesUpTo D Lam) a f)) (w := solPrices c tc tq) hN (listsOf D (cLam a)).1 (D.fam (cLam a)).d (listsOf D (cLam a)).2.1 (listsOf D (cLam a)).2.2 (askCost c (cLam a)) hI hd hl₀ hl₁ h₀ h₁ (fun _ => rfl) h6
    rw [hlen] at h
    exact h
  have hemp : a.1.1.isEmpty = false := by
    rcases h : a.1.1 with _ | ⟨u, t⟩
    · have h2 : a.1.1.length = l + 1 := hl
      rw [h] at h2
      exact absurd h2 (by simp)
    · rfl
  have hsol := mapOut_within (g := (Sum.inl : ℤ → Ans)) (mapIn_within (g := (Prod.fst : Ctx → Head)) (a := a) (ite_within_false (p := fun a : Head => a.1.isEmpty) (M := baseSolver x₀) hemp hlev))
  rw [division_exact hExp hS Bound hF hl]
  refine QueryMachine.Within.mono hsol ?_ ?_
  · have hnP : nPatterns (readyOf D x₀ a.1) = #(D.fam (cLam a)).I ^ nRectG (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) := nPatterns_ready D x₀ a.1 hl
    rw [hnP]
    have k1 : 1 ≤ Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l := Nat.one_le_pow _ _ (K_pos x₀ l)
    have k2 : (Cg + 3) * Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l ≤ Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ C * Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l := Nat.mul_le_mul_right _ hc1
    have k3 : (Cg + 3) * Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l = Cg * Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l + 3 * Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l := by ring
    have k4 : #(D.fam (cLam a)).I ^ nRectG (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) * (Cg * Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l + (tc + 2) + 1) ≤ #(D.fam (cLam a)).I ^ nRectG (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) * (Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ C * Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l + tc) := Nat.mul_le_mul_left _ (by omega)
    omega
  · exact le_trans (by omega) hroom
end ExplicitCost
