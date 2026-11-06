-- Prove2me | solution 1 for Eight.ViaGrouping.Cost.bound_follows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:43:10.855024+00:00
-- url     : https://prove2.me/submissions/89174dda-4e72-43ba-9311-377d291eec30

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Search
import Definitions.Def_StepMachines_Math_RebalanceArith
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Main
import Theorems.Thm_Eight_ViaGrouping_Cost_terms_le
import Theorems.Thm_Eight_ViaGrouping_Cost_exponent_le
import Theorems.Thm_Eight_ViaGrouping_Cost_base_le
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
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
open Eight.ViaGrouping.Cost
namespace Eight.ViaGrouping.Cost
theorem _root_.solution {K g : ℕ} (A c₁ s : ℕ) {e : ℝ} (hK : 1 ≤ K) (hg : 1 ≤ g) (h0 : 0 ≤ e) :
    ∃ A' : ℕ, ∀ P B τ U TE T : ℕ, 1 ≤ P → 1 ≤ τ → U ≤ g * P →
      (TE : ℝ) ≤ A * (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * (Paper.groupedLength K g U P : ℝ)) * ((Bp K g P B : ℝ) + (Paper.groupedLength K g U P : ℝ)) ^ A
        * ((c₁ * 2 ^ (P * (2 * g / K)) * τ : ℕ) : ℝ) →
      T ≤ s + TE →
      (T : ℝ) ≤ A' * (2 : ℝ) ^ (e * U + (e + 2) * ((g : ℝ) * P) / K) * ((P : ℝ) + B) ^ A' * τ := by
  obtain ⟨E₀, hE₀⟩ : ∃ E₀ : ℕ, E₀ = ⌈e * (K : ℝ) ^ 2⌉₊ := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = 4 * g + g ^ 2 := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = A * D ^ A * c₁ * 2 ^ E₀ := ⟨_, rfl⟩
  refine ⟨A + s + M, fun P B τ U TE T hP hτ hU hTE hT => ?_⟩
  obtain ⟨A', hA'⟩ : ∃ A' : ℕ, A' = A + s + M := ⟨_, rfl⟩
  rw [← hA']
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = Paper.groupedLength K g U P := ⟨_, rfl⟩
  rw [← hL] at hTE
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (2 : ℝ) ^ (e * U + (e + 2) * ((g : ℝ) * P) / K) := ⟨_, rfl⟩
  rw [← hX]
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = (P : ℝ) + B := ⟨_, rfl⟩
  rw [← hY]
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = ((2 ^ (P * (2 * g / K)) : ℕ) : ℝ) := ⟨_, rfl⟩
  have hn0 : 0 ≤ n := hn ▸ Nat.cast_nonneg _
  have hX1 : 1 ≤ X := hX ▸ Real.one_le_rpow (by norm_num) (by positivity)
  have hY1 : 1 ≤ Y := by
    rw [hY]
    exact_mod_cast (by omega : 1 ≤ P + B)
  have hτ1 : (1 : ℝ) ≤ τ := by exact_mod_cast hτ
  have hYA : Y ^ A ≤ Y ^ A' := pow_le_pow_right₀ hY1 (by omega)
  have hYA1 : 1 ≤ Y ^ A' := one_le_pow₀ hY1
  have hbase : (Bp K g P B : ℝ) + L ≤ D * Y := by
    rw [hY, hD, hL]
    exact_mod_cast base_le U P B hK hg hP hU
  have hexp : (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * L) * n ≤ (2 : ℝ) ^ E₀ * X := by
    calc (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * L) * n ≤ (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * L) * (2 : ℝ) ^ (2 * ((g : ℝ) * P) / K) :=
          mul_le_mul_of_nonneg_left (hn ▸ terms_le K g P) (Real.rpow_pos_of_pos (by norm_num) _).le
      _ ≤ (2 : ℝ) ^ E₀ * X := by
          rw [hX, ← Real.rpow_natCast 2 E₀, ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          have h1 := exponent_le (K := K) g U P hK h0
          have h2 : e * (K : ℝ) ^ 2 ≤ E₀ := hE₀ ▸ Nat.le_ceil _
          rw [← hL] at h1
          linarith
  have hcost : ((c₁ * 2 ^ (P * (2 * g / K)) * τ : ℕ) : ℝ) = c₁ * n * τ := by rw [hn]; push_cast; ring
  have hTE' : (TE : ℝ) ≤ M * (X * Y ^ A' * τ) := by
    calc (TE : ℝ) ≤ A * (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * L) * ((Bp K g P B : ℝ) + L) ^ A * (c₁ * n * τ) := hcost ▸ hTE
      _ ≤ A * (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * L) * ((D : ℝ) * Y) ^ A * (c₁ * n * τ) := by gcongr
      _ = A * (D : ℝ) ^ A * c₁ * ((2 : ℝ) ^ (e * (K : ℝ) ^ 2 * L) * n) * Y ^ A * τ := by rw [mul_pow]; ring
      _ ≤ A * (D : ℝ) ^ A * c₁ * ((2 : ℝ) ^ E₀ * X) * Y ^ A' * τ := by gcongr
      _ = M * (X * Y ^ A' * τ) := by rw [hM]; push_cast; ring
  have hone : 1 ≤ X * Y ^ A' * τ := by
    have := mul_le_mul (mul_le_mul hX1 hYA1 zero_le_one (by linarith)) hτ1 zero_le_one (by positivity)
    simpa using this
  have hT' : (T : ℝ) ≤ s + TE := by exact_mod_cast hT
  calc (T : ℝ) ≤ s * (X * Y ^ A' * τ) + M * (X * Y ^ A' * τ) := by
        have : (s : ℝ) ≤ s * (X * Y ^ A' * τ) := le_mul_of_one_le_right (by positivity) hone
        linarith
    _ ≤ A' * (X * Y ^ A' * τ) := by
        rw [← add_mul]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hA']
        push_cast
        have : (0 : ℝ) ≤ A := by positivity
        linarith
    _ = A' * X * Y ^ A' * τ := by ring
end Eight.ViaGrouping.Cost
