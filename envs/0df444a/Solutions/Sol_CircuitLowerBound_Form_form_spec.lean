-- Prove2me | solution 1 for CircuitLowerBound.Form.form_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:18:11.798945+00:00
-- url     : https://prove2.me/submissions/889e2d0f-533f-4d7e-a835-cfbec349ba4b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_ToTuring_Lib_Int
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Nat1b
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Form
import Theorems.Thm_CircuitLowerBound_Form_exists_ge
import Theorems.Thm_CircuitLowerBound_Form_shape_tseitin
import Theorems.Thm_CircuitLowerBound_Form_length_check
import Theorems.Thm_CircuitLowerBound_Form_wf_check
import Theorems.Thm_CircuitLowerBound_Form_check_out
import Theorems.Thm_CircuitLowerBound_Form_sat_psi
import Theorems.Thm_CircuitLowerBound_Form_take_drop_eq
import Theorems.Thm_CircuitLowerBound_Form_not_all_iff
import Theorems.Thm_Groundwork_PolyT_dedup
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
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
import Theorems.Thm_Groundwork_ofWord_lt
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
import Theorems.Thm_Groundwork_toWord_ofWord
attribute [local fun_prop] Groundwork.PolyT.dedup
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
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
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Form
namespace CircuitLowerBound.Form
theorem _root_.solution {e : MCode} {L P : ℕ} (hFit : Fits e L P) {G : List GateD} {o : List ℕ} {C : List GateD} (hG : WF (nb e L) G)
    (ho : o.length = 3 * (L + 1)) (hoN : ∀ w ∈ o, w < nb e L + G.length)
    (hval : ∀ j < 2 ^ nb e L, ∀ i < 3,
      (ofWord (((o.drop (i * (L + 1))).take L).map fun w => (wires (toWord (nb e L) j) (toC G)).getD w false),
        (wires (toWord (nb e L) j) (toC G)).getD (o.getD (i * (L + 1) + L) 0) false) = (clauseAt e L P j).getD i (0, false))
    (hC : WF L C) :
    Shaped3 (nb e L + (check L (nb e L + G.length) G o C).length)
        (tseitin (nb e L) (check L (nb e L + G.length) G o C) ++ [[(nb e L + (check L (nb e L + G.length) G o C).length - 1, true)]]).dedup ∧
      (Sat (tseitin (nb e L) (check L (nb e L + G.length) G o C) ++ [[(nb e L + (check L (nb e L + G.length) G o C).length - 1, true)]]).dedup ↔
        ¬∀ D ∈ tabF e L P, ∃ l ∈ D, eval (toC C) (toWord L l.1) = l.2) := by
  obtain ⟨hf1, hf2⟩ := hFit
  have hL : 1 ≤ L := by omega
  have hn : 1 ≤ nb e L := by
    have : bt e L ≠ 0 := fun h0 => by
      rw [h0, pow_zero] at hf2
      omega
    unfold nb
    omega
  have ho' : ∀ i, o.getD i 0 < nb e L + G.length := by
    intro i
    rcases Nat.lt_or_ge i o.length with h | h
    · rw [List.getD_eq_getElem _ _ h]
      exact hoN _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ h]
      omega
  have hK := wf_check hL hG hC ho'
  have hout : nb e L + (check L (nb e L + G.length) G o C).length - 1 = nb e L + G.length + C.length + C.length + C.length + 4 := by
    rw [length_check]
    omega
  -- the three literals of clause number j, read off the output wires of G
  have lit : ∀ j < 2 ^ nb e L, ∀ i < 3,
      ((List.range L).map fun k => (wires (toWord (nb e L) j) (toC G)).getD (o.getD (i * (L + 1) + k) 0) false)
          = toWord L ((clauseAt e L P j).getD i (0, false)).1 ∧
        (wires (toWord (nb e L) j) (toC G)).getD (o.getD (i * (L + 1) + L) 0) false = ((clauseAt e L P j).getD i (0, false)).2 := by
    intro j hj i hi
    have h := hval j hj i hi
    rw [take_drop_eq o (i * (L + 1)) L (by rw [ho]; interval_cases i <;> omega), List.map_map] at h
    obtain ⟨h1, h2⟩ := Prod.ext_iff.1 h
    simp only at h1 h2
    have h3 := toWord_ofWord ((List.range L).map ((fun w => (wires (toWord (nb e L) j) (toC G)).getD w false) ∘ fun k => o.getD (i * (L + 1) + k) 0))
    rw [List.length_map, List.length_range, h1] at h3
    exact ⟨h3.symm, h2⟩
  -- what the last wire says
  have viol : ∀ (a : ℕ → Bool) (j : ℕ), j < 2 ^ nb e L → GE a (nb e L) (check L (nb e L + G.length) G o C) → (List.range (nb e L)).map a = toWord (nb e L) j →
      (a (nb e L + G.length + C.length + C.length + C.length + 4) = true ↔ ∀ l ∈ clauseAt e L P j, eval (toC C) (toWord L l.1) ≠ l.2) := by
    intro a j hj hE hx
    rw [check_out a hL hG hC ho' hE, hx]
    have l0 := lit j hj 0 (by norm_num)
    have l1 := lit j hj 1 (by norm_num)
    have l2 := lit j hj 2 (by norm_num)
    simp only [Nat.zero_mul, Nat.one_mul, Nat.two_mul] at l0 l1 l2
    have hc : clauseAt e L P j = [(clauseAt e L P j).getD 0 (0, false), (clauseAt e L P j).getD 1 (0, false), (clauseAt e L P j).getD 2 (0, false)] := rfl
    rw [hc]
    simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    rw [l0.1, l0.2, l1.1, l1.2, l2.1, l2.2]
  refine ⟨⟨fun D hD => ?_, List.nodup_dedup _⟩, ?_⟩
  · rcases List.mem_append.1 (List.mem_dedup.1 hD) with h | h
    · exact shape_tseitin _ _ hK D h
    · rw [List.mem_singleton] at h
      subst h
      refine ⟨by simp, fun l hl => ?_⟩
      rw [List.mem_singleton] at hl
      subst hl
      simp only
      omega
  · rw [sat_psi, not_all_iff e L P fun i => eval (toC C) (toWord L i), hout]
    constructor
    · rintro ⟨a, hE, ha⟩
      have hx : ((List.range (nb e L)).map a).length = nb e L := by simp
      have hj : ofWord ((List.range (nb e L)).map a) < 2 ^ nb e L := by
        have := ofWord_lt ((List.range (nb e L)).map a)
        rwa [hx] at this
      have hw : (List.range (nb e L)).map a = toWord (nb e L) (ofWord ((List.range (nb e L)).map a)) := by
        have := toWord_ofWord ((List.range (nb e L)).map a)
        rw [hx] at this
        exact this.symm
      exact ⟨_, hj, (viol a _ hj hE hw).1 ha⟩
    · rintro ⟨j, hj, hv⟩
      obtain ⟨a, hE, hx⟩ := exists_ge (nb e L) _ hK (toWord (nb e L) j) (length_toWord _ _)
      exact ⟨a, hE, (viol a j hj hE hx).2 hv⟩
end CircuitLowerBound.Form
