-- Prove2me | solution 1 for ExplicitCost.solverBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:37:00.770269+00:00
-- url     : https://prove2.me/submissions/20382f07-e335-4671-b706-77fd484f8d34

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CliqueReads
import Definitions.Def_CountedRecursion_Brute
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Base
import Theorems.Thm_ExplicitCost_size_listUnit
import Theorems.Thm_ExplicitCost_tables_readTables
import Theorems.Thm_ExplicitCost_base_room_le
import Theorems.Thm_ExplicitCost_brute_within
import Theorems.Thm_ExplicitCost_ite_within_true
import Theorems.Thm_ExplicitCost_mapAsk_within
import Theorems.Thm_ExplicitCost_mapIn_within
import Theorems.Thm_ExplicitCost_mapOut_within
import Theorems.Thm_ExplicitCost_readAs_within
import Theorems.Thm_ExplicitCost_readTables_setting
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_mono
import Theorems.Thm_QueryMachines_QueryMachine_Runs_mono
import Theorems.Thm_QueryMachines_QueryMachine_WithinFrom_mono
import Theorems.Thm_QueryMachines_QueryMachine_Within_mono
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local simp] Groundwork.mem_words
attribute [local simp] Groundwork.size_prod



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution : SolverBase := by
  refine ⟨6, fun D c x₀ Bound gl a f hF h0 tc tq => ?_⟩
  obtain ⟨hl, hB, W, hW, hf⟩ := hF
  have hK : Levels.Gen.K x₀ (cLev a) = 2 ^ x₀ := by rw [h0]; rfl
  rw [hK] at hW hf
  subst hf
  change (solver c x₀).Within _ _ a _ _ (Sum.inl (clique (Levels.Gen.K x₀ (cLev a)) (cLam a) fun w => readTables (answersOf (2 ^ x₀) (cLam a) W) w.val).value)
  rw [hK]
  -- brute force, for the tables read back from the oracle
  have b := brute_within (2 ^ x₀) a.1.2 (readTables (answersOf (2 ^ x₀) (cLam a) W)) (fun w hw z hz => by
    rw [readTables_setting (lam := cLam a) W hw (mem_words.1 hz)]
    exact hW w hw z hz) tq
  have eT : tables (2 ^ x₀) a.1.2.1.length (readTables (answersOf (2 ^ x₀) (cLam a) W)) = tables (2 ^ x₀) (cLam a) W := tables_readTables _ _ _
  rw [eT] at b
  -- the oracle of the solver, at a query to the tables, read as an integer
  have eO : (fun q : TableQuery => ((spec D c x₀ Bound).oracle gl a (answersOf (2 ^ x₀) (cLam a) W) (Sum.inr (Sum.inl q))).map asInt) = tables (2 ^ x₀) (cLam a) W := funext fun q => by
    change ((tables (2 ^ x₀) (cLam a) W q).map Sum.inl).map asInt = _
    cases tables (2 ^ x₀) (cLam a) W q <;> rfl
  have hE : (fun h : Head => h.1.isEmpty) a.1 = true := by
    have : a.1.1.length = 0 := h0
    change a.1.1.isEmpty = true
    rw [List.isEmpty_iff, ← List.length_eq_zero_iff]
    exact this
  have r : (solver c x₀).Within ((spec D c x₀ Bound).oracle gl a (answersOf (2 ^ x₀) (cLam a) W)) (solPrices c tc tq) a _ _ _ :=
    mapOut_within (mapIn_within (ite_within_true hE (mapIn_within (readAs_within (O := fun x => ((spec D c x₀ Bound).oracle gl a (answersOf (2 ^ x₀) (cLam a) W) x).map asInt) (fun _ => rfl)
      (mapAsk_within (h := fun q : TableQuery => (Sum.inr (Sum.inl q) : SolQuery)) (w := solPrices c tc tq) (by rw [eO]; exact b))))))
  refine r.mono le_rfl ?_
  have hs : size a.1.2 = 2 * cLam a + 1 + (2 * cB a + 1) := by
    rw [size_prod, size_listUnit, size_listUnit]
    rfl
  rw [hs]
  exact base_room_le Nat.one_le_two_pow hl hB
end ExplicitCost
