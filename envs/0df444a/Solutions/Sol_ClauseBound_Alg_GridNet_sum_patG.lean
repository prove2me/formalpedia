-- Prove2me | solution 1 for ClauseBound.Alg.GridNet.sum_patG
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:16:16.559431+00:00
-- url     : https://prove2.me/submissions/f8ab784f-8ae6-4b7f-9d3e-575159b6c03f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Grid_Size
import Definitions.Def_ClauseBound_Grid_Expand
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_ClauseBound_Alg_GridNet
import Theorems.Thm_ClauseBound_Alg_GridNet_ixG_bijOn
import Theorems.Thm_Groundwork_Prog_sum_digits
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
import Theorems.Thm_Groundwork_mem_tuples
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
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridNet
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
namespace ClauseBound.Alg.GridNet
theorem _root_.solution (p d n : ℕ) (F : (Rect (Fin p) (Fin d) → ℕ) → ℤ) :
    ∑ y ∈ range ((n + 1) ^ nRectG p d), F (patG p d n y) =
      ∑ ι ∈ tuples (fun ω => ω ∈ Ω (Fin p) (Fin d)) (fun _ => range (n + 1)) 0, F ι := by
  have hlt : ∀ ω ∈ Ω (Fin p) (Fin d), ixG p d ω < nRectG p d := fun ω hω =>
    Finset.mem_range.1 (Finset.mem_coe.1 ((ixG_bijOn p d).mapsTo (Finset.mem_coe.2 hω)))
  set E : (Fin (nRectG p d) → ℕ) → Rect (Fin p) (Fin d) → ℕ :=
    fun φ ω => if h : ω ∈ Ω (Fin p) (Fin d) then φ ⟨ixG p d ω, hlt ω h⟩ else 0 with hE
  have h1 : ∀ y, patG p d n y = E fun q => digit n y q := by
    intro y
    funext ω
    simp only [patG, hE]
    split_ifs <;> rfl
  have hs : ∀ q : Fin (nRectG p d), ∃ ω ∈ Ω (Fin p) (Fin d), ixG p d ω = q := fun q => by
    obtain ⟨ω, hω, hq⟩ := (ixG_bijOn p d).surjOn (Finset.mem_coe.2 (Finset.mem_range.2 q.2))
    exact ⟨ω, Finset.mem_coe.1 hω, hq⟩
  choose inv hinv1 hinv2 using hs
  simp only [h1]
  rw [Prog.sum_digits n (nRectG p d) fun φ => F (E φ)]
  refine Finset.sum_nbij E ?_ ?_ ?_ fun _ _ => rfl
  · intro φ hφ
    rw [mem_tuples]
    refine fun ω => ⟨fun h => ?_, fun h => ?_⟩
    · simp only [hE, dif_pos h]
      exact Fintype.mem_piFinset.1 hφ _
    · simp only [hE, dif_neg h]
  · intro φ _ φ' _ heq
    funext q
    have h2 := congrFun heq (inv q)
    simp only [hE, dif_pos (hinv1 q)] at h2
    have hq : (⟨ixG p d (inv q), hlt _ (hinv1 q)⟩ : Fin (nRectG p d)) = q := Fin.ext (hinv2 q)
    rwa [hq] at h2
  · intro ι hι
    have hι' := (mem_tuples _ _ _ _).1 (Finset.mem_coe.1 hι)
    refine ⟨fun q => ι (inv q), Finset.mem_coe.2 (Fintype.mem_piFinset.2 fun q => (hι' (inv q)).1 (hinv1 q)), ?_⟩
    funext ω
    by_cases h : ω ∈ Ω (Fin p) (Fin d)
    · simp only [hE, dif_pos h]
      exact congrArg ι ((ixG_bijOn p d).injOn (Finset.mem_coe.2 (hinv1 _)) (Finset.mem_coe.2 h) (hinv2 _))
    · simp only [hE, dif_neg h]
      exact ((hι' ω).2 h).symm
end ClauseBound.Alg.GridNet
