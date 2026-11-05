-- Prove2me | solution 1 for ClauseBound.Alg.GridNet.gridN_sized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:15:48.296423+00:00
-- url     : https://prove2.me/submissions/8ad79515-3df1-4544-b02c-4dc4cfe5da14

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Grid_Size
import Definitions.Def_ClauseBound_Grid_Expand
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_ClauseBound_Alg_GridNet
import Theorems.Thm_ClauseBound_Alg_GridNet_nParts_mul_nMemb
import Theorems.Thm_ClauseBound_Alg_GridNet_abs_gridR_le
import Theorems.Thm_ClauseBound_Alg_GridNet_digG_lt
import Theorems.Thm_ClauseBound_Alg_GridNet_abs_trA_le
import Theorems.Thm_ClauseBound_Grid_rowNet_sized_pd
import Theorems.Thm_Groundwork_Network_sized_pull_of_le
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
import Theorems.Thm_Groundwork_card_words
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
variable {P : PiecesF} {pad : U} {h ℓ : ℕ} {A : ℕ → Pieces.Four ℓ}
namespace ClauseBound.Alg.GridNet
theorem _root_.solution (hP : CutsOK P pad h ℓ A) (p d : ℕ) (tr : Bool) (y : ℕ) {B : ℕ} {Rm : Inst (Fin (p * d)) (List Bool)}
    (hR : BoundedInst ℓ B Rm) :
    (gridN P pad p d tr h ℓ y Rm).Sized (P.m * (nParts p d tr * nMemb p d tr ^ 2 * ℓ))
      (nMemb p d tr * B + nMemb p d tr ^ 2 * P.bits h ℓ) := by
  refine Network.sized_pull_of_le _ _ _ _ (ClauseBound.Grid.rowNet_sized_pd hP.m_pos (Fintype.card_fin _) (Fintype.card_fin _) (by simp) _
    (abs_gridR_le tr hR) _ _ (fun ω => hP.factors tr _ (digG_lt hP.cnt_pos d tr y _ _)) (fun ω => (card_words _).le)
    (fun ω => hP.cap_le tr _ (digG_lt hP.cnt_pos d tr y _ _)) (fun ω => hP.abs_top tr _ (digG_lt hP.cnt_pos d tr y _ _))
    (fun ω => hP.abs_bot tr _ (digG_lt hP.cnt_pos d tr y _ _))
    (fun ω => abs_trA_le (hP.abs_A _ (digG_lt hP.cnt_pos d tr y _ _)) tr)) fun _ => ?_
  rw [← nParts_mul_nMemb p d tr]
  refine le_trans (le_of_eq ?_) (Nat.le_mul_of_pos_left _ hP.m_pos)
  ring
end ClauseBound.Alg.GridNet
