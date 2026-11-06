-- Prove2me | solution 1 for Eight.ViaGrouping.netAlg_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:54:10.414336+00:00
-- url     : https://prove2.me/submissions/120bedeb-593e-4dee-b8b0-bc0462a26ede

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Search
import Definitions.Def_StepMachines_Math_RebalanceArith
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Main
import Theorems.Thm_Eight_ViaGrouping_Cost_Bp_le
import Theorems.Thm_Eight_ViaGrouping_Cost_bound_follows
import Theorems.Thm_Eight_ViaGrouping_Cost_run_clique
import Theorems.Thm_Eight_SecNetworks_K2L_le
import Theorems.Thm_Eight_SecNetworks_U_le
import Theorems.Thm_Eight_ViaGrouping_searchP_runs
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_RebalanceArith_size_le
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_optBind_runs_some
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
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
import Theorems.Thm_Paper_Achievable_mono
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea
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
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Cost
namespace Eight.ViaGrouping
theorem _root_.solution (hT : StTable) (hV : StValue) {K g : ℕ} {e : ℝ} {E : Paper.CliqueAlgorithm} (hK : 2 ≤ K) (hKg : K ≤ g) (h0 : 0 ≤ e) (h : E.Within K e)
    (hS : ∀ (C : Type) [HasSize C] (Np : Procs C) (c : C) (N : Net g) (P B τ S : ℕ), IsNetworkP Np c N P B τ S →
      ∃ x < K ^ g, (List.range (K ^ g)).find? (fun x => goodP K g Np (c, x)) = some x ∧ Good N.c P (Paper.grouping (g := g) (by omega : 0 < K) x)) :
    Correct (netAlg K g E) g K e (e + 2) := by
  have hK0 : 0 < K := by omega
  -- the constants
  obtain ⟨A, c₁, hc₁1, hrunE⟩ := run_clique hT hV g hK0 (by omega) h
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : ℕ, c₂ = c₁ + 5 * size (K ^ g) + 20 := ⟨_, rfl⟩
  obtain ⟨A1, hA1⟩ := bound_follows (K := K) (g := g) A c₁ (2 * K ^ g + 1) (by omega) (by omega) h0
  obtain ⟨A2, hA2⟩ := RebalanceArith.size_le (K := K) (g := g) A c₂ (2 * g + g ^ 2) hK hKg
  refine ⟨max A1 A2, fun C _ Np c N P B τ S hN => ?_⟩
  have hP := hN.is.P_pos
  have hU := U_le hN.is
  -- «fix the first good one», number x
  obtain ⟨x, hxlt, hfind, hgood⟩ := hS C Np c N P B τ S hN
  have hsearch := searchP_runs K g Np c
  rw [hfind] at hsearch
  -- «run the algorithm for (K, e) …»
  obtain ⟨TE, hrun, hTE⟩ := hrunE C Np c N P B τ S hN x hxlt hgood
  have hall := optBind_runs_some (dflt := zeroOf) hsearch hrun
  have hZ1 : 1 ≤ size c + P + B := by omega
  have hpow : ∀ {a b : ℕ}, a ≤ b → a * (size c + P + B) ^ a ≤ b * (size c + P + B) ^ b := fun hab =>
    Nat.mul_le_mul hab (Nat.pow_le_pow_right hZ1 hab)
  refine ⟨2 * K ^ g + 1 + TE, hall.mono le_rfl ?_, ?_⟩
  · -- the sizes of the states
    refine (hA2 P B N.U (Paper.groupedLength K g N.U P) (Bp K g P B) S (S + c₁ * (size c + P + B) ^ c₁) (size c) (size (c, x)) _ hP hU (K2L_le K g N.U P)
      (Bp_le g P B (by omega)) (Nat.add_le_add_left (hpow (by omega)) _) ?_ ?_).trans (Nat.add_le_add_left (hpow (le_max_right _ _)) _)
    · have hx : size x ≤ size (K ^ g) := by
        simp only [size_nat]
        exact Nat.succ_le_succ (Nat.size_le_size hxlt.le)
      have h3 : size c + size (K ^ g) ≤ c₂ * (size c + P) := by
        have h4 : 1 * size c ≤ c₂ * size c := Nat.mul_le_mul_right _ (by omega)
        have h5 : c₂ * 1 ≤ c₂ * P := Nat.mul_le_mul_left _ hP
        rw [Nat.mul_add]
        omega
      simp only [size_prod]
      omega
    · have h3 : c₂ * (size c + P + B) ≤ c₂ * (size c + P + B) ^ c₂ :=
        Nat.mul_le_mul_left _ (Nat.le_self_pow (by omega) _)
      have h4 : 5 * size c + 5 * size (K ^ g) + 20 ≤ c₂ * (size c + P + B) := by
        have h5 : 5 * size c ≤ c₂ * size c := Nat.mul_le_mul_right _ (by omega)
        have h6 : c₂ * 1 ≤ c₂ * P := Nat.mul_le_mul_left _ hP
        rw [Nat.mul_add, Nat.mul_add]
        omega
      omega
  · -- «the bound follows»
    refine (hA1 P B τ N.U TE (2 * K ^ g + 1 + TE) hP hN.τ_pos hU hTE le_rfl).trans ?_
    have hY : (1 : ℝ) ≤ (P : ℝ) + B := by exact_mod_cast (by omega : 1 ≤ P + B)
    have hAm : (A1 : ℝ) ≤ ((max A1 A2 : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
    have hYp : ((P : ℝ) + B) ^ A1 ≤ ((P : ℝ) + B) ^ (max A1 A2) := pow_le_pow_right₀ hY (le_max_left _ _)
    gcongr
end Eight.ViaGrouping
