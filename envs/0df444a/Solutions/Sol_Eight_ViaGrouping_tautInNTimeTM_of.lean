-- Prove2me | solution 1 for Eight.ViaGrouping.tautInNTimeTM_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:17:06.305081+00:00
-- url     : https://prove2.me/submissions/31d18dd9-5000-435e-ada0-62be695ba295

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_NSETH
import Definitions.Def_Eight_ViaGrouping_CorDefs2
import Definitions.Def_GraphProblems_Host
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_CorNSETH
import Theorems.Thm_Eight_ViaGrouping_verifier_polyTimeSteps
import Theorems.Thm_Eight_ViaGrouping_verifier_recognizes
import Theorems.Thm_CircuitLowerBound_Alg_outputs_unique
import Theorems.Thm_GraphProblems_tm_of_stepped
import Theorems.Thm_Groundwork_DecodeK_length_enc_succ_le
import Theorems.Thm_Groundwork_Decode_length_enc_succ_le
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
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



set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Paper Turing
open Classical
namespace Eight.ViaGrouping
theorem _root_.solution (k : ℕ) {δ : ℝ} (hδ : 0 < δ) {M : StepMachine (List Bool) Bool} (hp : PolyTimeSteps M) {c : ℕ} (hM : Decides M k (δ / 2) c) : TautInNTimeTM k δ := by
  obtain ⟨hI⟩ := verifier_polyTimeSteps hp
  have h := verifier_recognizes hM
  obtain ⟨a₀, ha₀⟩ : ∃ a₀, a₀ = k * 2 ^ k + 1 := ⟨_, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ c', c' = c * a₀ ^ c + (k + 1) * c := ⟨_, rfl⟩
  obtain ⟨N, C, hfin, hN⟩ := GraphProblems.tm_of_stepped (verifier M) (ι := (n : ℕ) × {ψ : DNF n // IsKDNF k ψ} × List Bool)
    (fun x => withWitness x.2.2 (SatK.enc k x.2.1.1)) (fun x => [decide (Tautology x.2.1.1)]) (fun x => x.1 + x.2.2.length) hδ c' (a₀ + 2) (k + 1)
    (fun x => by
      obtain ⟨n, ⟨ψ, hψ⟩, w⟩ := x
      have hl : (SatK.enc k ψ).length + 1 ≤ a₀ * (n + 2) ^ (k + 1) := ha₀ ▸ DecodeK.length_enc_succ_le hψ
      have h1 : (n + 2) ^ (k + 1) ≤ (n + w.length + 2) ^ (k + 1) := Nat.pow_le_pow_left (by omega) _
      have h2 : n + w.length + 2 ≤ (n + w.length + 2) ^ (k + 1) := Nat.le_self_pow (by omega) _
      have h3 := Nat.mul_le_mul_left a₀ h1
      simp only [withWitness, List.length_append, List.length_replicate, List.length_cons]
      rw [add_mul]
      omega)
    (fun x => by
      obtain ⟨n, ⟨ψ, hψ⟩, w⟩ := x
      obtain ⟨T, b, hr, hb, hT⟩ := h n ψ hψ w
      have hbd : b = decide (Tautology ψ) := by
        by_cases ht : Tautology ψ
        · simp [ht, hb.2 ht]
        · cases b
          · simp [ht]
          · exact absurd (hb.1 rfl) ht
      have hl : (SatK.enc k ψ).length + 1 ≤ a₀ * (n + 2) ^ (k + 1) := ha₀ ▸ DecodeK.length_enc_succ_le hψ
      have hcc : c ≤ c' := by
        have h1 : 1 ≤ a₀ ^ c := Nat.one_le_pow _ _ (by omega)
        rw [hc']
        exact (Nat.le_mul_of_pos_right c h1).trans (Nat.le_add_right _ _)
      refine ⟨T, hbd ▸ hr.mono le_rfl ?_, hT.trans ?_⟩
      · calc c * ((SatK.enc k ψ).length + 1) ^ c ≤ c * (a₀ * (n + 2) ^ (k + 1)) ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hl c)
          _ = (c * a₀ ^ c) * (n + 2) ^ ((k + 1) * c) := by rw [mul_pow, ← pow_mul, mul_assoc]
          _ ≤ c' * (n + w.length + 2) ^ c' := by
            rw [hc']
            exact Nat.mul_le_mul (Nat.le_add_right _ _) ((Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (Nat.le_add_left _ _)))
      · have h5 : (2 : ℝ) ^ (δ / 2 * n) ≤ (2 : ℝ) ^ (δ / 2 * ((n + w.length : ℕ) : ℝ)) := by
          refine Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left ?_ (by positivity))
          exact_mod_cast Nat.le_add_right _ _
        have h6 : (c : ℝ) ≤ c' := by exact_mod_cast hcc
        exact mul_le_mul h6 h5 (by positivity) (by positivity))
  refine ⟨N, C, hfin, fun n ψ hψ => ⟨fun ht => ⟨[], ?_⟩, ?_⟩⟩
  · have h1 := hN ⟨n, ⟨ψ, hψ⟩, []⟩
    simpa [ht] using h1
  · rintro ⟨w, ⟨ev⟩⟩
    obtain ⟨ev'⟩ := hN ⟨n, ⟨ψ, hψ⟩, w⟩
    have h5 := CircuitLowerBound.Alg.outputs_unique ev ev'
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h5
    have h6 := N.outputAlphabet.symm.injective h5
    exact of_decide_eq_true h6.symm
end Eight.ViaGrouping
