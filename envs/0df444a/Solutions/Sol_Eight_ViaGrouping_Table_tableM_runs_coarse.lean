-- Prove2me | solution 1 for Eight.ViaGrouping.Table.tableM_runs_coarse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:50:28.581743+00:00
-- url     : https://prove2.me/submissions/dfb674ba-8bd9-4915-b0c6-1aa1007ee2cf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Table
import Theorems.Thm_Eight_ViaGrouping_Table_tableM_runs
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
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Table
variable {C : Type} [HasSize C] {K g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
variable {x β : ℕ} {G : Fin K} {θ : Fin K → List Bool}
namespace Eight.ViaGrouping.Table
theorem _root_.solution (K g : ℕ) : ∃ c₁ : ℕ, 1 ≤ c₁ ∧ ∀ (C : Type) [HasSize C] (Np : Procs C) (c : C) (N : Net g) (P B τ S : ℕ), IsNetworkP Np c N P B τ S →
    ∀ x < K ^ g, ∀ β ≤ 2 * (g * P), ∀ m ≤ 2 * g, (∀ G < K, (members K g x G).length ≤ m) → (∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g Np.toPaperNetwork c x G G' ≤ β) →
    ∀ (G : Fin K) (θ : Fin K → List Bool), (∀ G', G' ≠ G → (θ G').length = β) → θ G = [] →
    (tableM K g Np).Runs ((c, x), (G.val, List.ofFn θ)) (c₁ * 2 ^ (P * m) * τ) (S + c₁ * (size c + P + B) ^ c₁) (mergedVal K g Np.toPaperNetwork N.toPaperNetwork ((c, x), (G.val, List.ofFn θ))) := by
  obtain ⟨sx, hsx⟩ : ∃ sx, sx = size (K ^ g) := ⟨_, rfl⟩
  obtain ⟨sK, hsK⟩ : ∃ sK, sK = size K := ⟨_, rfl⟩
  obtain ⟨sg, hsg⟩ : ∃ sg, sg = size (g * g) := ⟨_, rfl⟩
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, c₀ = 4 + 4 * sx + 4 * sK + (16 * (K * g) + 8 * K) + 10 * g + 2 * (g * g) + 3 * sg + 30 := ⟨_, rfl⟩
  refine ⟨c₀ + (8 * (g * g) + 1), by omega, ?_⟩
  intro C _ Np c N P B τ S h x hx β hβ m hm hmem hlb G θ hθ hG
  have hτ := h.τ_pos
  have hP := h.is.P_pos
  refine (tableM_runs h m hmem hlb hθ hG).mono ?_ ?_
  · generalize 2 ^ (P * m) = a
    calc a * (g * g * (4 * τ + 4) + 1) ≤ a * (g * g * (8 * τ) + τ) := Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) hτ)
      _ = (8 * (g * g) + 1) * a * τ := by ring
      _ ≤ (c₀ + (8 * (g * g) + 1)) * a * τ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))
  · obtain ⟨X, hX⟩ : ∃ X, X = size c + P + B := ⟨_, rfl⟩
    rw [← hX]
    have hX1 : 1 ≤ X := by omega
    have e1 : size x ≤ sx * X := by
      have : size x ≤ sx := by
        have := Nat.size_le_size hx.le
        simp only [hsx, size_nat]
        omega
      exact this.trans (Nat.le_mul_of_pos_right _ hX1)
    have e2 : sK ≤ sK * X := Nat.le_mul_of_pos_right _ hX1
    have e3 : K * (2 * β + 2) ≤ (4 * (K * g) + 2 * K) * X := by
      calc K * (2 * β + 2) ≤ K * (2 * (2 * (g * P)) + 2) := Nat.mul_le_mul_left _ (by omega)
        _ = 4 * (K * g) * P + 2 * K * 1 := by ring
        _ ≤ 4 * (K * g) * X + 2 * K * X := Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) (Nat.mul_le_mul_left _ hX1)
        _ = (4 * (K * g) + 2 * K) * X := by ring
    have e4 : P * m ≤ 2 * g * X := by
      calc P * m ≤ X * (2 * g) := Nat.mul_le_mul (by omega) hm
        _ = 2 * g * X := by ring
    have e5 : B * (g * g) ≤ g * g * X := by
      calc B * (g * g) ≤ X * (g * g) := Nat.mul_le_mul_right _ (by omega)
        _ = g * g * X := by ring
    have e6 : sg ≤ sg * X := Nat.le_mul_of_pos_right _ hX1
    have e7 : c₀ * X = 4 * X + 4 * (sx * X) + 4 * (sK * X) + 4 * ((4 * (K * g) + 2 * K) * X) + 5 * (2 * g * X) + 2 * (g * g * X) + 3 * (sg * X) + 30 * X := by
      rw [hc₀]
      ring
    have e8 : c₀ * X ≤ (c₀ + (8 * (g * g) + 1)) * X ^ (c₀ + (8 * (g * g) + 1)) := Nat.mul_le_mul (by omega) (Nat.le_self_pow (by omega) X)
    rw [← hsK, ← hsg]
    omega
end Eight.ViaGrouping.Table
