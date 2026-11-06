-- Prove2me | solution 1 for ExplicitCost.brute_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:28:13.699975+00:00
-- url     : https://prove2.me/submissions/4d9f276d-c897-48bc-95fa-016d01515d2f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Within
import Definitions.Def_Printed_Coding
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Brute
import Theorems.Thm_ExplicitCost_clique_value_eq
import Theorems.Thm_ExplicitCost_mapIn_within
import Theorems.Thm_ExplicitCost_prodRange_within
import Theorems.Thm_ExplicitCost_query_within
import Theorems.Thm_ExplicitCost_sumRange_within
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_natAbs_prod_le
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
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
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_length_block
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_query0_eq
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
import Theorems.Thm_Groundwork_star_labelling_ne
import Theorems.Thm_Groundwork_star_labelling_self
import Theorems.Thm_Groundwork_sum_blocks_pairs
import Theorems.Thm_Groundwork_sum_toWord
import Theorems.Thm_Groundwork_tri_lt
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Printed_length_flatten_ofFn
import Theorems.Thm_Printed_size_entry
import Theorems.Thm_Printed_size_ofFn_le
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
attribute [local fun_prop] Groundwork.PolyT.const
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
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (K : ℕ) (c : List Unit × List Unit) (W : ℕ → List Bool → ℤ) (hW : ∀ w < K, ∀ z ∈ words ((K - 1) * c.1.length), |W w z| < 2 ^ c.2.length) (tq : ℕ) :
    (bruteMachine K).Within (tables K c.1.length W) (fun _ => tq) c (2 ^ (K * (K - 1) / 2 * c.1.length) * (K * (tq + 1) + 1))
      (3 * size c + 3 * (K * (K - 1) / 2 * c.1.length) + 2 * (c.2.length * K) + 2 * size K + K * (2 * c.1.length + 2) + c.2.length + 13) (clique K c.1.length fun w => W w.val).value := by
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = c.1.length := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = c.2.length := ⟨_, rfl⟩
  rw [← hlam, ← hB] at hW ⊢
  obtain ⟨n, hn⟩ : ∃ n, n = K * (K - 1) / 2 * lam := ⟨_, rfl⟩
  rw [← hn]
  -- the strings at the node v under the choice number y
  let θ : ℕ → Fin K → Fin K → List Bool := fun y v => star (labelling K lam [] (toWord n y)) v
  have hθ : ∀ y (v u : Fin K), u ≠ v → (θ y v u).length = lam := fun y v u hu => by
    change (star (labelling K lam [] (toWord n y)) v u).length = lam
    rw [star_labelling_ne _ _ _ _ hu]
    refine length_block ?_
    rw [length_toWord, hn]
    have hne : v.1 ≠ u.1 := fun h => hu (Fin.ext h.symm)
    exact Nat.mul_le_mul_right _ (tri_lt (min_lt_max.2 hne) (max_lt v.2 u.2))
  have hθ0 : ∀ y (v : Fin K), θ y v v = [] := fun y v => star_labelling_self _ _ _ _ v
  have hθle : ∀ y (v u : Fin K), (θ y v u).length ≤ lam := fun y v u => by
    by_cases hu : u = v
    · rw [hu, hθ0]
      exact Nat.zero_le _
    · exact (hθ y v u hu).le
  let val : ℕ → ℕ → ℤ := fun y v => if h : v < K then listTables K W ⟨v, h⟩ (θ y ⟨v, h⟩) else 1
  have hval : ∀ y (v : Fin K), val y v.val = listTables K W v (θ y v) := fun y v => by simp only [val, v.2, dif_pos]
  have hfl : ∀ y (v : Fin K), (List.ofFn (θ y v)).flatten.length = (K - 1) * lam := fun y v => length_flatten_ofFn v _ (hθ y v) (hθ0 y v)
  have hb : ∀ y (v : Fin K), |val y v.val| < 2 ^ B := fun y v => by
    rw [hval]
    exact hW v.val v.2 _ (mem_words.2 (hfl y v))
  have hb' : ∀ y, ∀ v < K, (val y v).natAbs ≤ 2 ^ B := fun y v hv => by
    have := hb y ⟨v, hv⟩
    rw [Int.abs_eq_natAbs] at this
    exact_mod_cast this.le
  -- one entry: one query
  have hq : ∀ y (v : Fin K), (QueryMachine.mapIn (bruteQuery K (fun c : List Unit × List Unit => c.1.length) nilC) askTable).Within (tables K lam W) (fun _ => tq) ((c, y), v.val) tq
      (size c + size K + (K * (2 * lam + 2) + 1) + (B + 1) + 1) (val y v.val) := fun y v => by
    have e : bruteQuery K (fun c : List Unit × List Unit => c.1.length) nilC ((c, y), v.val) = (c, (v.val, List.ofFn (θ y v))) := by
      change (c, query0 K c.1.length [] (toWord (K * (K - 1) / 2 * c.1.length) y) v.val) = _
      rw [← hlam, ← hn, query0_eq]
    have hO : tables K lam W (toTable (bruteQuery K (fun c : List Unit × List Unit => c.1.length) nilC ((c, y), v.val)).2) = some (val y v.val) := by
      rw [e, hval]
      exact if_pos ⟨v.2, hfl y v⟩
    refine (mapIn_within (query_within (h := fun x : (List Unit × List Unit) × IQ => toTable x.2) (w := fun _ => tq) hO)).mono le_rfl ?_
    rw [e]
    have h1 := size_ofFn_le (θ y v) (hθle y v)
    have h2 := size_entry (hb y v)
    have h3 := Nat.size_le_size v.2.le
    simp only [size_prod, size_nat] at h1 h2 h3 ⊢
    omega
  -- one term: K entries
  have hin : ∀ y < 2 ^ n, (QueryMachine.prodRange (Function.const ((List Unit × List Unit) × ℕ) K) (QueryMachine.mapIn (bruteQuery K (fun c : List Unit × List Unit => c.1.length) nilC) askTable)).Within
      (tables K lam W) (fun _ => tq) (c, y) (K * (tq + 1)) (size c + size (2 ^ n) + size K + (size ((2 ^ B) ^ K) + (size c + size K + (K * (2 * lam + 2) + 1) + (B + 1) + 1)) + 1)
      (∏ v ∈ range K, val y v) := fun y hy => by
    have := prodRange_within (N := Function.const ((List Unit × List Unit) × ℕ) K) (a := (c, y)) (fun _ => tq) (val y) (2 ^ B) _ Nat.one_le_two_pow (fun v hv => hq y ⟨v, hv⟩) (hb' y)
    simp only [Function.const_apply] at this
    refine this.mono (by simp) ?_
    have := Nat.size_le_size hy.le
    simp only [size_prod, size_nat]
    omega
  -- all terms
  have hout : (bruteMachine K).Within (tables K lam W) (fun _ => tq) c (∑ _y ∈ range (2 ^ n), (K * (tq + 1) + 1))
      (size c + size (2 ^ n) + (size (2 ^ n * (2 ^ B) ^ K) + (size c + size (2 ^ n) + size K + (size ((2 ^ B) ^ K) + (size c + size K + (K * (2 * lam + 2) + 1) + (B + 1) + 1)) + 1)) + 1)
      (∑ y ∈ range (2 ^ n), ∏ v ∈ range K, val y v) := by
    have e : bruteBound K (fun c : List Unit × List Unit => c.1.length) c = 2 ^ n := by rw [hn, hlam]; rfl
    have := sumRange_within (N := bruteBound K fun c : List Unit × List Unit => c.1.length) (a := c) (fun _ => K * (tq + 1)) (fun y => ∏ v ∈ range K, val y v) ((2 ^ B) ^ K) _
      (fun y hy => hin y (e ▸ hy)) (fun y _ => Stepped.natAbs_prod_le (val y) (2 ^ B) K (hb' y))
    rw [e] at this
    exact this
  have e1 : ∑ _y ∈ range (2 ^ n), (K * (tq + 1) + 1) = 2 ^ n * (K * (tq + 1) + 1) := by simp
  have e2 : ∑ y ∈ range (2 ^ n), ∏ v ∈ range K, val y v = Inst.ZW lam [] (listTables K W) := by
    unfold Inst.ZW
    rw [← sum_blocks_pairs K lam [] fun Λ => ∏ v, listTables K W v (star Λ v), ← hn, ← sum_toWord]
    refine sum_congr rfl fun y _ => ?_
    rw [prod_range]
    exact prod_congr rfl fun v _ => hval y v
  rw [e1, e2] at hout
  rw [clique_value_eq]
  refine hout.mono le_rfl ?_
  rw [← pow_mul, ← pow_add]
  simp only [size_nat, Nat.size_pow]
  omega
end ExplicitCost
