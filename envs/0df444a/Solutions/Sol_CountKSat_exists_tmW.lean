-- Prove2me | solution 1 for CountKSat.exists_tmW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:59:22.513165+00:00
-- url     : https://prove2.me/submissions/04789384-493c-44cf-ac82-5ac36913e736

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_ToTuring_Machine_Host
import Definitions.Def_CountKSat_Host
import Theorems.Thm_CountKSat_HostW_epilogue_within
import Theorems.Thm_CountKSat_HostW_size_le_of_reaches
import Theorems.Thm_CountKSat_HostW_look_within
import Theorems.Thm_CountKSat_HostW_mainLoop_within
import Theorems.Thm_Groundwork_Host_look_within
import Theorems.Thm_Groundwork_Host_mainLoop_within
import Theorems.Thm_Groundwork_Host_outputs_of_within
import Theorems.Thm_Groundwork_Host_prologue_within
import Theorems.Thm_Groundwork_Host_size_le_of_reaches
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_Host_within_io
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_seq
import Theorems.Thm_Groundwork_TM_beq_LR
import Theorems.Thm_Groundwork_TM_beq_RL
import Theorems.Thm_Groundwork_TM_beq_bL
import Theorems.Thm_Groundwork_TM_beq_bR
import Theorems.Thm_Groundwork_TM_dropF_within
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
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f
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
open CountKSat
open Groundwork Groundwork.TM Groundwork.Host Turing HostW
namespace CountKSat
theorem _root_.solution (M : Stepped (List Bool) (List Bool)) [IsPolyT M] :
    ∃ (N : TM2ComputableAux Bool Bool) (q : ℕ), (∀ k, Finite (N.tm.Γ k)) ∧
      ∀ (x : List Bool) (T S : ℕ) (w : List Bool), M.Runs x T S w →
        Nonempty (TM2OutputsInTime N.tm (x.map N.inputAlphabet.invFun) (some (w.map N.outputAlphabet.invFun))
          (q * (T + 1) * (x.length + S + 1) ^ q)) := by
  obtain ⟨Pi, tI, pI, mI, hI, -⟩ := (IsPolyT.init (M := M)).elim
  obtain ⟨Ps, tS, pS, mS, hS, -⟩ := (IsPolyT.step (M := M)).elim
  obtain ⟨Po, tO, pO, mO, hO, lO⟩ := (IsPolyT.out (M := M)).elim
  have pL : PB fun m => 7 * m := (PB.const 7).mul PB.id'
  have pO' : PB fun m => tO (7 * m) := pO.comp pL
  have pK : PB fun m => 3 * (7 * m) + 3 + tO (7 * m) := (((PB.const 3).mul pL).add (PB.const 3)).add pO'
  have pG : PB fun m => 1 + (tS (7 * m) + (3 * (7 * m) + 3 + tO (7 * m))) := (PB.const 1).add ((pS.comp pL).add pK)
  have pQ : PB fun m => (4 * m + 3 + (tI (3 * m + 2) + (3 * (7 * m) + 3 + tO (7 * m))) + 1 + (4 * tO (7 * m) + 3) +
      (7 * m + 1)) + (1 + (tS (7 * m) + (3 * (7 * m) + 3 + tO (7 * m)))) :=
    (((((((PB.const 4).mul PB.id').add (PB.const 3)).add
      ((pI.comp (((PB.const 3).mul PB.id').add (PB.const 2))).add pK)).add (PB.const 1)).add
      (((PB.const 4).mul pO').add (PB.const 3))).add (pL.add (PB.const 1))).add pG
  obtain ⟨q, hq⟩ := pQ
  refine ⟨⟨tmOf (HostW.prog Pi Ps Po), Equiv.refl _, Equiv.refl _⟩, q, fun k => ?_, fun x T S w hr => ?_⟩
  · rcases k with _ | k
    · exact inferInstanceAs (Finite Bool)
    · exact inferInstanceAs (Finite Sym)
  · obtain ⟨m, hm⟩ : ∃ m, m = x.length + S := ⟨_, rfl⟩
    obtain ⟨L, hLdef⟩ : ∃ L, L = 7 * m := ⟨_, rfl⟩
    have hL : ∀ s : M.σ, size s ≤ S → len s ≤ L := fun s hs => by
      have h1 := Carried.le s
      omega
    obtain ⟨s', hs', ho', h3⟩ := HostW.mainLoop_within hS hO mS mO hL hr
    have h1 := prologue_within x
    have h2 := within_io ((hI x [] [] [] []).seq (HostW.look_within hO (M.init x) [] [] [] [])) []
    have h4 := epilogue_within w (wd s' ++ []) [] []
    have h5 := within_io (dropF_within (Enc.toV s') [] [] [] []) w
    rw [List.append_nil] at h2
    have h := (((h1.seq h2).seq h3).seq h4).seq h5
    have hq' := hq m
    dsimp only at hq'
    rw [← hLdef] at hq'
    refine outputs_of_within (h.mono ?_) (List.map_id x) (List.map_id w)
    have g1 := hL _ (HostW.size_le_of_reaches hr)
    have g2 := mO g1
    have g3 : (code (Enc.toV s')).length ≤ L := hL s' hs'
    have g4 : len x = 3 * x.length + 2 := len_bools x
    have g6 : tI (3 * x.length + 2) ≤ tI (3 * m + 2) := mI (by omega)
    have g7 : w.length ≤ tO L := by
      have a1 := lO s'
      rw [ho', len_some, len_bools] at a1
      have a2 := mO (hL s' hs')
      omega
    rw [g4]
    obtain ⟨G, hG⟩ : ∃ G, G = 1 + (tS L + (3 * L + 3 + tO L)) := ⟨_, rfl⟩
    rw [← hG] at hq' ⊢
    rw [← hm]
    obtain ⟨Y, hY⟩ : ∃ Y, Y = q * (m + 1) ^ q := ⟨_, rfl⟩
    have e : q * (T + 1) * (m + 1) ^ q = T * Y + Y := by rw [hY]; ring
    rw [e]
    rw [← hY] at hq'
    have g5 : T * G ≤ T * Y := Nat.mul_le_mul_left _ (by omega)
    omega
end CountKSat
