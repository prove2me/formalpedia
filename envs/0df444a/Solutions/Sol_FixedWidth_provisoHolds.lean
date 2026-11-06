-- Prove2me | solution 1 for FixedWidth.provisoHolds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:18:01.713204+00:00
-- url     : https://prove2.me/submissions/53a595b8-2f70-436d-a46e-302d6704b2ab

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FixedWidthSteps_RouteDefs
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_GeneralPieces_Num_Between
import Definitions.Def_GeneralPieces_Num_Remarks
import Definitions.Def_FixedWidthSteps_Numbers
import Theorems.Thm_ClauseBound_Gen_Pick_next_polyT
import Theorems.Thm_ClauseBound_Inst_Rec_ccF_polyT
import Theorems.Thm_ClauseBound_Inst_Rec_chooseZ_polyT
import Theorems.Thm_ClauseBound_Inst_Rec_factN_polyT
import Theorems.Thm_ClauseBound_Inst_Rec_fallZ_polyT
import Theorems.Thm_ClauseBound_Inst_Rec_linF_polyT
import Theorems.Thm_ClauseBound_Inst_Rec_muF_polyT
import Theorems.Thm_ClauseBound_Inst_Rec_muF_unary
import Theorems.Thm_ClauseBound_Inst_Rec_nbF_polyT
import Theorems.Thm_ClauseBound_Inst_Rec_nbF_unary
import Theorems.Thm_ClauseBound_Inst_Rec_nblk_polyT
import Theorems.Thm_ClauseBound_Inst_Rec_nblk_unary
import Theorems.Thm_ClauseBound_Inst_Rec_phiF_polyT
import Theorems.Thm_ClauseBound_Inst_Rec_powZ_polyT
import Theorems.Thm_ClauseBound_Inst_Rec_qqF_polyT
import Theorems.Thm_ClauseBound_Inst_Rec_sgnZ_polyT
import Theorems.Thm_ClauseBound_Inst_Rec_unary_min_right
import Theorems.Thm_GeneralPieces_Between_between_half
import Theorems.Thm_GeneralPieces_Between_eleven_pow
import Theorems.Thm_GeneralPieces_Between_num_den_polyT
import Theorems.Thm_Groundwork_DecodeK_clauseDec_polyT
import Theorems.Thm_Groundwork_Decode_clauseDec_polyT
import Theorems.Thm_Groundwork_Decode_slotDec_polyT
import Theorems.Thm_Groundwork_Decode_width_polyT
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_any
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_contains
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_countP
import Theorems.Thm_Groundwork_PolyT_decide_mem
import Theorems.Thm_Groundwork_PolyT_dedup
import Theorems.Thm_Groundwork_PolyT_div
import Theorems.Thm_Groundwork_PolyT_div_pow
import Theorems.Thm_Groundwork_PolyT_dropWhile
import Theorems.Thm_Groundwork_PolyT_elem
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_filterMap
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_idxOf
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_mod
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_PolyT_optionElim
import Theorems.Thm_Groundwork_PolyT_pow_const
import Theorems.Thm_Groundwork_PolyT_prodMk
import Theorems.Thm_Groundwork_PolyT_product
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_PolyT_sprod
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_PolyT_sumElim
import Theorems.Thm_Groundwork_PolyT_takeWhile
import Theorems.Thm_Groundwork_PolyT_testBit
import Theorems.Thm_Groundwork_Prog_NetE_Pc_polyT
import Theorems.Thm_Groundwork_Prog_NetE_betaC_polyT
import Theorems.Thm_Groundwork_Prog_NetE_capWord_polyT
import Theorems.Thm_Groundwork_Prog_NetE_cap_polyT
import Theorems.Thm_Groundwork_Prog_NetE_col_polyT
import Theorems.Thm_Groundwork_Prog_NetE_lAt_polyT
import Theorems.Thm_Groundwork_Prog_NetE_labOf_polyT
import Theorems.Thm_Groundwork_Prog_NetE_lbLen_polyT
import Theorems.Thm_Groundwork_Prog_NetE_lbLens_polyT
import Theorems.Thm_Groundwork_Prog_NetE_members_polyT
import Theorems.Thm_Groundwork_Prog_NetE_n_polyT
import Theorems.Thm_Groundwork_Prog_NetE_prs_polyT
import Theorems.Thm_Groundwork_Prog_NetE_stLens_polyT
import Theorems.Thm_Groundwork_Prog_NetE_zA_polyT
import Theorems.Thm_Groundwork_Prog_NetE_zAt_polyT
import Theorems.Thm_Groundwork_Prog_NetE_zOf_polyT
import Theorems.Thm_Groundwork_Sparsify_polyT_addP
import Theorems.Thm_Groundwork_Sparsify_polyT_canonP
import Theorems.Thm_Groundwork_Sparsify_polyT_greedyP
import Theorems.Thm_Groundwork_Sparsify_polyT_litsOf
import Theorems.Thm_Groundwork_Sparsify_polyT_minusP
import Theorems.Thm_Groundwork_Sparsify_polyT_overP
import Theorems.Thm_Groundwork_Sparsify_polyT_pickP
import Theorems.Thm_Groundwork_Sparsify_polyT_redP
import Theorems.Thm_Groundwork_Sparsify_polyT_rootP
import Theorems.Thm_Groundwork_Sparsify_polyT_stepP
import Theorems.Thm_Groundwork_Sparsify_polyT_subP
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
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_block_polyT
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_query0_polyT
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
import Theorems.Thm_Groundwork_tri_polyT
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_chunks__bc5b8682856d
import Theorems.Thm_P2M_Groundwork_PolyT_cond__4c673073da15
import Theorems.Thm_P2M_Groundwork_PolyT_cons__3a60f43a3b86
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_P2M_Groundwork_PolyT_inl__78f4b62d65a1
import Theorems.Thm_P2M_Groundwork_PolyT_inr__53ca1f30b2d3
import Theorems.Thm_P2M_Groundwork_PolyT_ite__226169acf219
import Theorems.Thm_P2M_Groundwork_PolyT_log2__935ea318e2e8
import Theorems.Thm_P2M_Groundwork_PolyT_ofWord__0eb069943014
import Theorems.Thm_P2M_Groundwork_PolyT_size__c8c8eb1b342f
import Theorems.Thm_P2M_Groundwork_PolyT_some__e6a32bd6af45
import Theorems.Thm_PaddedDescent_F_cap_polyT
attribute [local fun_prop] ClauseBound.Gen.Pick.next_polyT
attribute [local fun_prop] ClauseBound.Inst.Rec.ccF_polyT
attribute [local fun_prop] ClauseBound.Inst.Rec.chooseZ_polyT
attribute [local fun_prop] ClauseBound.Inst.Rec.factN_polyT
attribute [local fun_prop] ClauseBound.Inst.Rec.fallZ_polyT
attribute [local fun_prop] ClauseBound.Inst.Rec.linF_polyT
attribute [local fun_prop] ClauseBound.Inst.Rec.muF_polyT
attribute [local fun_prop] ClauseBound.Inst.Rec.muF_unary
attribute [local fun_prop] ClauseBound.Inst.Rec.nbF_polyT
attribute [local fun_prop] ClauseBound.Inst.Rec.nbF_unary
attribute [local fun_prop] ClauseBound.Inst.Rec.nblk_polyT
attribute [local fun_prop] ClauseBound.Inst.Rec.nblk_unary
attribute [local fun_prop] ClauseBound.Inst.Rec.phiF_polyT
attribute [local fun_prop] ClauseBound.Inst.Rec.powZ_polyT
attribute [local fun_prop] ClauseBound.Inst.Rec.qqF_polyT
attribute [local fun_prop] ClauseBound.Inst.Rec.sgnZ_polyT
attribute [local fun_prop] ClauseBound.Inst.Rec.unary_min_right
attribute [local fun_prop] Groundwork.Decode.clauseDec_polyT
attribute [local fun_prop] Groundwork.Decode.slotDec_polyT
attribute [local fun_prop] Groundwork.Decode.width_polyT
attribute [local fun_prop] Groundwork.DecodeK.clauseDec_polyT
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.any
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.contains
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.countP
attribute [local fun_prop] Groundwork.PolyT.decide_mem
attribute [local fun_prop] Groundwork.PolyT.dedup
attribute [local fun_prop] Groundwork.PolyT.div
attribute [local fun_prop] Groundwork.PolyT.div_pow
attribute [local fun_prop] Groundwork.PolyT.dropWhile
attribute [local fun_prop] Groundwork.PolyT.elem
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.filterMap
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.idxOf
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.mod
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] Groundwork.PolyT.optionElim
attribute [local fun_prop] Groundwork.PolyT.pow_const
attribute [local fun_prop] Groundwork.PolyT.prodMk
attribute [local fun_prop] Groundwork.PolyT.product
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] Groundwork.PolyT.sprod
attribute [local fun_prop] Groundwork.PolyT.sum
attribute [local fun_prop] Groundwork.PolyT.sumElim
attribute [local fun_prop] Groundwork.PolyT.takeWhile
attribute [local fun_prop] Groundwork.PolyT.testBit
attribute [local fun_prop] Groundwork.Prog.NetE.Pc_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.betaC_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.capWord_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.cap_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.col_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.lAt_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.labOf_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.lbLen_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.lbLens_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.members_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.n_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.prs_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.stLens_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.zA_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.zAt_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.zOf_polyT
attribute [local fun_prop] Groundwork.Sparsify.polyT_addP
attribute [local fun_prop] Groundwork.Sparsify.polyT_canonP
attribute [local fun_prop] Groundwork.Sparsify.polyT_greedyP
attribute [local fun_prop] Groundwork.Sparsify.polyT_litsOf
attribute [local fun_prop] Groundwork.Sparsify.polyT_minusP
attribute [local fun_prop] Groundwork.Sparsify.polyT_overP
attribute [local fun_prop] Groundwork.Sparsify.polyT_pickP
attribute [local fun_prop] Groundwork.Sparsify.polyT_redP
attribute [local fun_prop] Groundwork.Sparsify.polyT_rootP
attribute [local fun_prop] Groundwork.Sparsify.polyT_stepP
attribute [local fun_prop] Groundwork.Sparsify.polyT_subP
attribute [local fun_prop] Groundwork.block_polyT
attribute [local fun_prop] Groundwork.query0_polyT
attribute [local fun_prop] Groundwork.tri_polyT
attribute [local fun_prop] P2M_Groundwork_PolyT_chunks__bc5b8682856d
attribute [local fun_prop] P2M_Groundwork_PolyT_cond__4c673073da15
attribute [local fun_prop] P2M_Groundwork_PolyT_cons__3a60f43a3b86
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] P2M_Groundwork_PolyT_inl__78f4b62d65a1
attribute [local fun_prop] P2M_Groundwork_PolyT_inr__53ca1f30b2d3
attribute [local fun_prop] P2M_Groundwork_PolyT_ite__226169acf219
attribute [local fun_prop] P2M_Groundwork_PolyT_log2__935ea318e2e8
attribute [local fun_prop] P2M_Groundwork_PolyT_ofWord__0eb069943014
attribute [local fun_prop] P2M_Groundwork_PolyT_size__c8c8eb1b342f
attribute [local fun_prop] P2M_Groundwork_PolyT_some__e6a32bd6af45
attribute [local fun_prop] PaddedDescent.F.cap_polyT
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
open FixedWidth
open Groundwork PaddedDescent.F
namespace FixedWidth
theorem _root_.solution : ProvisoHolds := by
  intro x₀
  refine ⟨⟨fun p => (11 ^ p.1.length, 12 ^ p.1.length), PolyT.comp (by fun_prop : PolyT fun u : U => (11 ^ u.length, 12 ^ u.length)) (PolyT.fst PolyT.id'), fun l => ?_⟩,
    ⟨fun p => (GeneralPieces.Between.num p.1.length, GeneralPieces.Between.den p.1.length), PolyT.comp GeneralPieces.Between.num_den_polyT (PolyT.fst PolyT.id'), fun l => ?_⟩⟩
  · dsimp only
    rw [List.length_replicate, GeneralPieces.Between.eleven_pow]
    have h : (0 : ℝ) ≤ (11 / 12) ^ l := by positivity
    exact ⟨by linarith, le_rfl⟩
  · dsimp only
    rw [List.length_replicate]
    exact GeneralPieces.Between.between_half l
end FixedWidth
