-- Prove2me | solution 1 for ClauseBound.Alg.GridPresents.gridFf_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:22:16.828244+00:00
-- url     : https://prove2.me/submissions/2bea367c-8d08-48d6-bcc3-79145c7b4c45

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_GridNet
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_ClauseBound_Alg_GridPresents
import Theorems.Thm_ClauseBound_Alg_GridPresents_prod_ind_range
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_Prog_prod_counter_pairs
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
import Theorems.Thm_PaddedDescent_F_prodL_eq
attribute [local fun_prop] Groundwork.PolyT.all
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
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridPresents
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg.GridNet
namespace ClauseBound.Alg.GridPresents
theorem _root_.solution (P : PiecesF) (pad : U) (p d : ℕ) (tr : Bool) (h ℓ y a b : ℕ) (z θ : List Bool) :
    gridFf P pad p d tr h ℓ y ((a, b), (z, θ)) =
      (∏ i : Fin (nMemb p d tr), if heG p d ℓ z i (nodeG d tr b i) = block ℓ i θ then 1 else 0) *
      ∏ k : Fin (nMemb p d tr) × Fin (nMemb p d tr) with k.1 < k.2, item P pad p d tr h ℓ y a b z θ k.1 k.2 := by
  have h1 : ∏ i : Fin (nMemb p d tr), (if heG p d ℓ z i (nodeG d tr b i) = block ℓ i θ then (1 : ℤ) else 0) =
      if ((List.range (nMemb p d tr)).all fun i => heG p d ℓ z i (nodeG d tr b i) == block ℓ i θ) = true then 1 else 0 := by
    rw [← prod_ind_range]
    simp only [beq_iff_eq]
  rw [h1, ← prod_counter_pairs (nMemb p d tr) fun i i' => item P pad p d tr h ℓ y a b z θ i i']
  unfold gridFf
  simp only [prodL_eq]
  cases (List.range (nMemb p d tr)).all fun i => heG p d ℓ z i (nodeG d tr b i) == block ℓ i θ with
  | false => simp
  | true => simp [item]
end ClauseBound.Alg.GridPresents
