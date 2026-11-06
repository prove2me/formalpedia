-- Prove2me | solution 1 for ExplicitCost.procedureCostFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:03:10.419687+00:00
-- url     : https://prove2.me/submissions/a8a9745a-9c33-440e-b75a-3f2a4a8dc71e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CallFacts
import Definitions.Def_CountedRecursion_ParentSize
import Definitions.Def_CountedRecursion_Within
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_ProcedureCost
import Theorems.Thm_ExplicitCost_procedure_arith
import Theorems.Thm_ExplicitCost_answersOf_some
import Theorems.Thm_ExplicitCost_at_call
import Theorems.Thm_ExplicitCost_entryCost_cast
import Theorems.Thm_ExplicitCost_fits_succ
import Theorems.Thm_ExplicitCost_groupTables_mkParent
import Theorems.Thm_ExplicitCost_length_unary
import Theorems.Thm_ExplicitCost_level_numbers
import Theorems.Thm_ExplicitCost_mapIn_within
import Theorems.Thm_ExplicitCost_mapOut_within
import Theorems.Thm_ExplicitCost_nParts_self
import Theorems.Thm_ExplicitCost_size_mkParent_le
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Printed_AchievedBy_mono
import Theorems.Thm_Printed_length_unary
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_mono
import Theorems.Thm_QueryMachines_QueryMachine_Runs_mono
import Theorems.Thm_QueryMachines_QueryMachine_WithinFrom_mono
import Theorems.Thm_QueryMachines_QueryMachine_Within_mono
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono
import Theorems.Thm_SingleBitPieces_Level_Presents_nParts_self


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution : ProcedureCostFrom := by
  intro hG hL hC hE hBN hLC hCB hSub c
  obtain ⟨c₁, hE⟩ := entryCost_cast hE
  obtain ⟨C₂, hB2⟩ := hBN c
  refine ⟨C₂ + (c + 4) * c₁ + (2 * c + 4) + 2, fun ρ x₀ D hS Bound a a' f l hF hl hc q v hq tq Lam hLam => ?_⟩
  obtain ⟨y, x, h⟩ := at_call hG hL hC hBN hS hF hl hc
  obtain ⟨hK2, hKg, hg2⟩ := level_numbers hS.x₀_ge l
  obtain ⟨hlam, hB1, hW, hf⟩ := fits_succ hF hl
  have hK0 : 0 < Levels.Gen.K x₀ l := by omega
  have hpK : pK (callParent D x₀ l a y x) = Levels.Gen.K x₀ l := length_unary _
  -- the query names a group γ and a setting Θ of it, and the answer is W̃_γ(Θ)
  have htab : (spec D c x₀ Bound).tab a' f = answersOf (Levels.Gen.K x₀ l) (callL D c x₀ l a f y) (groupTables D c (callParent D x₀ l a y x) (callL D c x₀ l a f y) (readTables f)) := by
    change answersOf (pK (parentOf a')) (cLam a') (groupTables D c (parentOf a') (cLam a') (readTables f)) = _
    rw [h.parent, h.lam, hpK]
  rw [htab] at hq
  obtain ⟨hq1, hq2, rfl⟩ := answersOf_some hq
  have hval : groupTables D c (callParent D x₀ l a y x) (callL D c x₀ l a f y) (readTables f) q.1 q.2 =
      (Value.groupClique asked.under (netInput (callNet D c x₀ l a f y) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) (callNet D c x₀ l a f y) hK0 x (callL D c x₀ l a f y)).W ⟨q.1, hq1⟩ q.2 := by
    unfold callParent
    rw [groupTables_mkParent]
    exact dif_pos hq1
  rw [hval]
  -- what the procedure hands to `entryData`
  have hin : calleeInput c (a', q) = (callParent D x₀ l a y x, ((((unary (Levels.Gen.K x₀ l), unary (Levels.Gen.g x₀ l)),
      netInput (callNet D c x₀ l a f y) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))), x), toLists (Levels.Gen.K x₀ l) (callL D c x₀ l a f y) ((⟨q.1, hq1⟩ : Fin (Levels.Gen.K x₀ l)).val, q.2))) := by
    change (parentOf a', ((netData c (parentOf a'), pX (parentOf a')), toLists (pK (parentOf a')) (cLam a') q)) = _
    rw [h.parent, h.lam, h.data, hpK]
    rfl
  -- «Crude bounds give L ≤ N + 1», for the L of the call; so L ≤ 2gP, which the cost of an entry
  -- asks
  have hLle : callL D c x₀ l a f y ≤ Levels.Gen.g x₀ l ^ 4 * cLam a + 1 :=
    hLC ρ c x₀ D hS l (cLam a) y (direction (readyOf D x₀ a.1, y)) (readTables f) hlam
  have hL2 : callL D c x₀ l a f y ≤ 2 * (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a)) := by
    have e : Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) = Levels.Gen.g x₀ l ^ 4 * cLam a := by ring
    have h1 : 1 ≤ Levels.Gen.g x₀ l ^ 4 * cLam a := Nat.mul_pos (Nat.pow_pos (by omega)) hlam
    omega
  -- an entry, at the price τ of a query of Definition 2(iii)
  have hent := (hE _ _ _ (nParts_self _ _) hK0 (callNet D c x₀ l a f y) _ _ ((askCost c (cLam a) + tq) * Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ C₂ + 2) hKg h.is (by omega) x h.x_lt _
    hL2 (h.few hK0) (h.short hK0) ⟨q.1, hq1⟩ q.2 hq2).1
  -- each such query is answered within τ − 2
  have hans := (hB2 ρ x₀ D hS (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (cLam a) (cB a) y x tq Lam (direction (readyOf D x₀ a.1, y)) (readTables f) hg2 hKg hlam hLam hB1 hW h.y_lt h.x_lt).2.2.2
  rw [← hf] at hans
  have hrun := hSub NetQuery ℤ UpQuery Ans Parent (X0 DataInput) ℤ entryData (gridProcsData c).answer (netOracle (callNet D c x₀ l a f y)) (Sum.elim f (piecesUpTo D Lam))
    (fun _ => (askCost c (cLam a) + tq) * Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ C₂ + 2) (upPrices c tq) (callParent D x₀ l a y x) _ _ _ _ _
    (fun _ => (askCost c (cLam a) + tq) * Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ C₂) hent hans (fun _ => le_rfl)
  -- the arithmetic
  have hX2 : 2 ≤ Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) := by
    have h1 : 1 * 2 ≤ Levels.Gen.g x₀ l ^ 2 * (cLam a + cB a) := Nat.mul_le_mul (Nat.one_le_pow _ _ (by omega)) (by omega)
    exact h1
  have hA : 2 ≤ askCost c (cLam a) + tq := by
    unfold askCost
    omega
  obtain ⟨hT, hSz⟩ := procedure_arith (C₂ := C₂) (c₁ := c₁) hX2 hA (hCB c x₀ l (cLam a) (cB a) 0 hS.x₀_ge hlam hB1 (Nat.zero_le _)).2.1
    (size_mkParent_le hS (direction (readyOf D x₀ a.1, y)) hKg hg2 hlam hB1 h.y_lt h.x_lt)
  unfold procedure
  refine mapOut_within (mapIn_within ?_)
  rw [hin]
  refine hrun.mono ?_ hSz
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ hT
end ExplicitCost
