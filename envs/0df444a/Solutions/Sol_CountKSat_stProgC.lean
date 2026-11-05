-- Prove2me | solution 1 for CountKSat.stProgC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:35:05.732525+00:00
-- url     : https://prove2.me/submissions/fc5c9d93-881b-457e-96db-009acd7b2ee8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_SparsifyWidthK_Refine
import Mathlib.Tactic.Ring
import Definitions.Def_CountKSat_ProgC
import Theorems.Thm_CountKSat_ProgC_sparsifiesC_of
import Theorems.Thm_Groundwork_PolyT_length
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
import Theorems.Thm_WidthK_ProgMain_iface
import Theorems.Thm_WidthK_ProgMain_mem_toFin
import Theorems.Thm_WidthK_Refine_mem_toFin
import Theorems.Thm_WidthK_Refine_stRefines
import Theorems.Thm_WidthK_stBetaSum
import Theorems.Thm_WidthK_stHeavyEq
import Theorems.Thm_WidthK_stLeafCard
import Theorems.Thm_WidthK_stLeafCount
import Theorems.Thm_WidthK_stLightEq
import Theorems.Thm_WidthK_stNodeBound
import Theorems.Thm_WidthK_stNodeRoot
import Theorems.Thm_WidthK_stNodeStep
import Theorems.Thm_WidthK_stSatIff
import Theorems.Thm_WidthK_stThr
attribute [local fun_prop] Groundwork.PolyT.length
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
open CountKSat
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog
namespace CountKSat
theorem _root_.solution (hSC : StStepCount) (hRC : StRootCount) (hSL : StSumLeaves) : StProgC := by
  intro τ k ε hτ hε n ψ hψ
  have hθ : ∀ i, 1 ≤ theta τ i := (stThr τ hτ).pos
  have hI := ProgMain.iface stNodeRoot stNodeStep stNodeBound stLeafCard stLightEq stHeavyEq stSatIff stThr stBetaSum hτ k n
  have hOk : ProgMain.Ok k n (toFin ψ) := by
    intro X hX
    obtain ⟨C, hC, rfl⟩ := ProgMain.mem_toFin.1 hX
    obtain ⟨a, b, c⟩ := hψ C hC
    refine ⟨fun l hl => ?_, (List.toFinset_nonempty_iff C).2 a, (List.toFinset_card_le C).trans b⟩
    rw [ProgMain.litsBelow, Finset.mem_product, Finset.mem_range]
    exact ⟨c l (List.mem_toFinset.1 hl), Finset.mem_univ _⟩
  have hT : k * n < (k * n / τ + 1) * τ := by
    calc k * n < τ * (k * n / τ + 1) := Nat.lt_mul_div_succ (k * n) (by omega : 0 < τ)
      _ = (k * n / τ + 1) * τ := Nat.mul_comm _ _
  obtain ⟨c1, c2, c3, c4⟩ := ProgC.sparsifiesC_of hSC hRC hSL hθ hI (Refine.stRefines _ k hθ) hT ψ hOk fun C hC => (hψ C hC).2
  have er : rootC (List.replicate n (), ψ) = (rootP ψ, taut n) := by simp [rootC]
  rw [er]
  refine ⟨?_, fun x hx => ?_, c3, fun i => ⟨(c4 i).1, fun x hx => ?_⟩⟩
  · exact (by exact_mod_cast c1 : ((leaves (stepC (theta τ) k) (bsum τ k * n) (rootP ψ, taut n)).length : ℝ) ≤
      ((∑ j ∈ range (k * n / τ + 1), (bsum τ k * n).choose j : ℕ) : ℝ)).trans (stLeafCount k τ ε hτ hε n)
  · obtain ⟨d1, d2, d3, d4⟩ := c2 x hx
    refine ⟨d1, d2.trans (le_of_eq ?_), d3, d4⟩
    ring
  · obtain ⟨d1, d2⟩ := (c4 i).2 x hx
    refine ⟨d1.trans ?_, d2⟩
    have e : (ψ.length + n) * (2 ^ k + k * bsum τ k + 1) =
        ψ.length * 2 ^ k + (n + k * (bsum τ k * n)) + (ψ.length * (k * bsum τ k + 1) + n * 2 ^ k) := by ring
    rw [e]
    exact Nat.le_add_right _ _
end CountKSat
