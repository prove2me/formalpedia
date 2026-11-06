-- Prove2me | solution 1 for CircuitLowerBound.Clause.core_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:05:00.493387+00:00
-- url     : https://prove2.me/submissions/c087ef22-fcbb-478b-b43a-b9ca65159f38

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Clause
import Theorems.Thm_CircuitLowerBound_Clause_length_selG
import Theorems.Thm_CircuitLowerBound_Clause_length_fldG
import Theorems.Thm_CircuitLowerBound_Clause_length_timeG
import Theorems.Thm_CircuitLowerBound_Clause_length_litG
import Theorems.Thm_CircuitLowerBound_Clause_time_val
import Theorems.Thm_CircuitLowerBound_Clause_pos_val
import Theorems.Thm_CircuitLowerBound_Clause_sel_val
import Theorems.Thm_CircuitLowerBound_Clause_Fw_val
import Theorems.Thm_CircuitLowerBound_Clause_wfa_gatesC
import Theorems.Thm_CircuitLowerBound_Clause_fbit_kind
import Theorems.Thm_CircuitLowerBound_Clause_fbit_dq
import Theorems.Thm_CircuitLowerBound_Blocks_getD_toWord
import Theorems.Thm_CircuitLowerBound_Blocks_gval_one
import Theorems.Thm_CircuitLowerBound_Blocks_gval_zero
import Theorems.Thm_CircuitLowerBound_Blocks_num_congr
import Theorems.Thm_CircuitLowerBound_Blocks_num_false
import Theorems.Thm_CircuitLowerBound_Blocks_num_testBit
import Theorems.Thm_CircuitLowerBound_Blocks_obeys_append
import Theorems.Thm_CircuitLowerBound_Blocks_obeys_flatMap
import Theorems.Thm_CircuitLowerBound_Blocks_obeys_wires
import Theorems.Thm_CircuitLowerBound_Blocks_ofWord_append
import Theorems.Thm_CircuitLowerBound_Blocks_wires_input
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_testBit
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
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.testBit
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



set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Clause
open ENP Groundwork CircuitLowerBound.Blocks
namespace CircuitLowerBound.Clause
theorem _root_.solution {n bq bt rb kbm Dq L P : ℕ} {tb : List TCl} (hn : n = rb + bt + bq) (hbt : 1 ≤ bt) (hR : tb.length < 2 ^ rb) (hL : bq + bt + 2 + kbm ≤ L)
    (hD : ∀ k ι i, Dq ≤ i → i < bq + 1 → (litI (tb.getD k zeroCl) ι).2.2.2.1.testBit i = false) {j : ℕ} (hj : j < 2 ^ n) {ι : ℕ} (hι : ι < 3)
    (v : ℕ → Bool) (hv : v = fun i => (wires (toWord n j) (toC (gatesC n bq bt rb kbm Dq P tb))).getD i false)
    (l : TLit) (hl : l = litI (tb.getD (j / 2 ^ (bt + bq)) zeroCl) ι) :
    ofWord (((outsL n bq bt rb tb.length kbm Dq L ι).take L).map v) =
      ((l.1 % 2 ^ kbm) * 2 ^ (bt + 1) + tval bt (j / 2 ^ bq % 2 ^ bt) l.2.1) * 2 ^ (bq + 1) + (qval P (j % 2 ^ bq) l.2.2.1 + l.2.2.2.1) % 2 ^ (bq + 1) ∧
    v ((outsL n bq bt rb tb.length kbm Dq L ι).getD L 0) = l.2.2.2.2 := by
  have hx : (toWord n j).length = n := length_toWord n j
  have hwf : WFa n (gatesC n bq bt rb kbm Dq P tb) := wfa_gatesC (by omega) (by omega) kbm Dq P tb
  have hob : Obeys v n (gatesC n bq bt rb kbm Dq P tb) := by
    have := obeys_wires (toWord n j) (gatesC n bq bt rb kbm Dq P tb) (by rw [hx]; exact hwf)
    rw [hx] at this
    rw [hv]
    exact this
  have hin : ∀ k < n, v k = j.testBit k := by
    intro k hk
    rw [hv]
    simp only
    rw [wires_input _ _ (by rw [hx]; exact hk), getD_toWord hk]
  rw [gatesC, obeys_append, obeys_append, obeys_append, obeys_flatMap v _ (k := szL bq bt) _ (length_litG n bq bt rb tb.length kbm Dq P) 3] at hob
  obtain ⟨⟨⟨hc, hsel⟩, hfld⟩, hlit⟩ := hob
  have e1 : n + ([(opZero, 0, 0), (opOne, 0, 0)] ++ selG n bq bt rb tb.length).length = n + 2 + rb * tb.length := by
    rw [List.length_append, length_selG]
    simp only [List.length_cons, List.length_nil]
    omega
  have e2 : n + ([(opZero, 0, 0), (opOne, 0, 0)] ++ selG n bq bt rb tb.length ++ fldG n rb kbm (5 + kbm + Dq) tb).length + szL bq bt * ι =
      offA n bq bt rb tb.length (5 + kbm + Dq) ι := by
    rw [List.length_append, List.length_append, length_selG, length_fldG, offA]
    simp only [List.length_cons, List.length_nil]
    omega
  rw [e1] at hfld
  have hlit' := hlit ι hι
  rw [e2, litG, obeys_append, length_timeG,
    show offA n bq bt rb tb.length (5 + kbm + Dq) ι + (3 * bt + 4) = offA n bq bt rb tb.length (5 + kbm + Dq) ι + 4 + 3 * bt by omega] at hlit'
  obtain ⟨htime, hpos⟩ := hlit'
  simp only [Obeys, gval_zero, gval_one, and_true] at hc
  obtain ⟨hZ, hO⟩ := hc
  -- the three parts of j
  have hrl : j / 2 ^ (bt + bq) < 2 ^ rb := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, ← Nat.add_assoc, ← hn]
    exact hj
  have hrb : ∀ i < rb, v (bq + bt + i) = (j / 2 ^ (bt + bq)).testBit i := by
    intro i hi
    rw [hin _ (by omega), Nat.testBit_div_two_pow, Nat.add_comm bq bt, Nat.add_comm i]
  have htb : ∀ i < bt, v (bq + i) = (j / 2 ^ bq % 2 ^ bt).testBit i := by
    intro i hi
    rw [hin _ (by omega), Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm i]
    simp [hi]
  have hqb : ∀ i < bq, v i = (j % 2 ^ bq).testBit i := by
    intro i hi
    rw [hin _ (by omega), Nat.testBit_mod_two_pow]
    simp [hi]
  have hE : ∀ k < tb.length, v (Ew n rb k) = decide (j / 2 ^ (bt + bq) = k) := fun k hk => sel_val hsel hO hrb hrl hk (hk.trans hR)
  have hF : ∀ f < 5 + kbm + Dq, v (Fw n rb tb.length (5 + kbm + Dq) ι f) = fbit kbm l f := fun f hf => by
    rw [hl]
    exact Fw_val hfld hZ hE hι hf
  have hT := time_val htime (md := l.2.1) (t := j / 2 ^ bq % 2 ^ bt) (by rw [hF 0 (by omega)]; rfl) (by rw [hF 1 (by omega)]; rfl) htb
    (Nat.mod_lt _ (by positivity))
  have hP := pos_val hpos (md := l.2.2.1) (q := j % 2 ^ bq) (dq := l.2.2.2.1) hZ (by rw [hF 2 (by omega)]; rfl) (by rw [hF 3 (by omega)]; rfl) hqb
    (Nat.mod_lt _ (by positivity)) (fun i hi => by
      unfold dWire
      split_ifs with h
      · rw [hF _ (by omega), fbit_dq]
      · rw [hZ, hl, hD _ _ i (by omega) hi])
  have hK : num (fun i => v (Fw n rb tb.length (5 + kbm + Dq) ι (5 + i))) kbm = l.1 % 2 ^ kbm := by
    rw [num_congr (c := l.1.testBit) fun i hi => by rw [hF _ (by omega), fbit_kind l hi], num_testBit]
  have hZs : num (fun _ => v n) (L - (bq + bt + 2 + kbm)) = 0 := by
    rw [hZ]
    exact num_false _
  unfold outsL
  constructor
  · rw [List.take_left' (by
      simp only [List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil]
      omega)]
    simp only [List.map_append, List.map_map, ofWord_append, List.length_append, List.length_map, List.length_range, List.map_cons, List.map_nil,
      List.length_cons, List.length_nil]
    change num (fun i => v (offA n bq bt rb tb.length (5 + kbm + Dq) ι + 4 + 3 * bt + 1 + 7 * i + 3)) (bq + 1) +
      2 ^ (bq + 1) * num (fun i => v (offA n bq bt rb tb.length (5 + kbm + Dq) ι + 3 + 3 * i + 1)) bt +
      2 ^ (bq + 1 + bt) * ofWord [v (offA n bq bt rb tb.length (5 + kbm + Dq) ι + 3 + 3 * bt)] +
      2 ^ (bq + 1 + bt + (0 + 1)) * num (fun i => v (Fw n rb tb.length (5 + kbm + Dq) ι (5 + i))) kbm +
      2 ^ (bq + 1 + bt + (0 + 1) + kbm) * num (fun _ => v n) (L - (bq + bt + 2 + kbm)) = _
    rw [hP, hK, hZs, ← hT]
    simp only [ofWord]
    ring
  · rw [List.getD_append_right _ _ _ _ (by
      simp only [List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil]
      omega)]
    have e : L - ((((List.range (bq + 1)).map fun i => offA n bq bt rb tb.length (5 + kbm + Dq) ι + 4 + 3 * bt + 1 + 7 * i + 3) ++
        ((List.range bt).map fun i => offA n bq bt rb tb.length (5 + kbm + Dq) ι + 3 + 3 * i + 1) ++ [offA n bq bt rb tb.length (5 + kbm + Dq) ι + 3 + 3 * bt] ++
        ((List.range kbm).map fun i => Fw n rb tb.length (5 + kbm + Dq) ι (5 + i)) ++ ((List.range (L - (bq + bt + 2 + kbm))).map fun _ => n)).length) = 0 := by
      simp only [List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil]
      omega
    rw [e, List.getD_cons_zero, hF 4 (by omega)]
    rfl
end CircuitLowerBound.Clause
