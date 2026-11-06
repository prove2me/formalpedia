-- Prove2me | solution 1 for CircuitLowerBound.Round.roundF_roundInput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:15:39.826434+00:00
-- url     : https://prove2.me/submissions/d3af0c9e-911f-4176-802f-72c86e4b1c9b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_PaddedDescent_Pad
import Definitions.Def_ToTuring_Poly_Decode
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_ENP_Round
import Theorems.Thm_CircuitLowerBound_Round_mU_roundInput
import Theorems.Thm_CircuitLowerBound_Round_xW_roundInput
import Theorems.Thm_CircuitLowerBound_Round_aW_roundInput
import Theorems.Thm_CircuitLowerBound_Round_encF_eq
import Theorems.Thm_CircuitLowerBound_Round_var_Phi_lt
import Theorems.Thm_CircuitLowerBound_Round_var_units_lt
import Theorems.Thm_CircuitLowerBound_Round_PhiF_eq
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
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
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
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



set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Round
variable {G : (MCode × List Unit × ℕ) × List Unit → Cnf} {fb : List Unit → Bool}
namespace CircuitLowerBound.Round
theorem _root_.solution (hG : ∀ (e : MCode) (L P : ℕ) (pad : List Unit), Fits e L P → 2 ^ nb e L ≤ pad.length → G ((e, List.replicate L (), P), pad) = tabF e L P)
    (hfb : ∀ m : ℕ, pos m = top (nu m) →
      (fb (List.replicate m ()) = true ↔ Fits (codeOf (nu m)) (2 ^ nu m) (2 ^ nu m) ∧ Sat (tabF (codeOf (nu m)) (2 ^ nu m) (2 ^ nu m))))
    (hV : StVars) (x ans : List Bool) (ha : ans.length ≤ 2 ^ x.length) {pad : List Unit} (hp : 2 ^ (2 * x.length + 4) ≤ pad.length) :
    roundF G fb (roundInput x ans, pad) =
      bif decide (ans.length ≤ ofWord x) then true :: encCnf (Phi x.length ++ units (ans.map (fun b => !b) ++ [false]))
      else [false, !ans.getD (ofWord x) false] := by
  have h1 : 2 ^ (2 * x.length) ≤ pad.length := (Nat.pow_le_pow_right (by norm_num) (by omega)).trans hp
  have h2 : 2 ^ x.length + 1 ≤ pad.length := by
    have a1 : 2 ^ (x.length + 1) ≤ 2 ^ (2 * x.length + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have a2 : 2 ^ (x.length + 1) = 2 ^ x.length * 2 := pow_succ 2 _
    have a3 : 1 ≤ 2 ^ x.length := Nat.one_le_two_pow
    omega
  simp only [roundF, aW_roundInput, xW_roundInput, mU_roundInput]
  rw [PhiF_eq hG hfb x.length h1, encF_eq]
  intro C hC l hl
  rcases List.mem_append.1 hC with hC | hC
  · have := var_Phi_lt hV x.length C hC l hl
    omega
  · have := var_units_lt _ C hC l hl
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at this
    omega
end CircuitLowerBound.Round
