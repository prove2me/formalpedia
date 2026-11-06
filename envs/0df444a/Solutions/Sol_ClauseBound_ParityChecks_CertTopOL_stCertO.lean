-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertTopOL.stCertO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:49:43.0512+00:00
-- url     : https://prove2.me/submissions/d40acd1d-4742-4ab9-acee-2e6ba1ed950a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_ClauseBound_TopN_Cert
import Definitions.Def_ClauseBound_Inst_RecArith
import Definitions.Def_ClauseBound_ParityChecks_CertTopOL
import Theorems.Thm_ClauseBound_ParityChecks_CertTopOL_planAtO_polyT
import Theorems.Thm_ClauseBound_Alg_CertCount_mu_polyT2
import Theorems.Thm_ClauseBound_Alg_CertCount_mu_unary2
import Theorems.Thm_ClauseBound_Alg_CertCount_rows_polyT2
import Theorems.Thm_ClauseBound_Alg_CertTop_PtopK_unary
import Theorems.Thm_ClauseBound_Alg_CertTop_capF_unary3
import Theorems.Thm_ClauseBound_Alg_CertTop_fF_polyT3
import Theorems.Thm_ClauseBound_Alg_CertTop_lamTopK_unary
import Theorems.Thm_ClauseBound_Alg_CertTop_linkB_polyT3
import Theorems.Thm_ClauseBound_Alg_CertTop_links_polyT3
import Theorems.Thm_ClauseBound_Alg_CertTop_litAt_polyT3
import Theorems.Thm_ClauseBound_Alg_CertTop_locals_polyT3
import Theorems.Thm_ClauseBound_Alg_CertTop_root9_polyT
import Theorems.Thm_ClauseBound_Alg_CertTop_slotsOf_polyT3
import Theorems.Thm_ClauseBound_Alg_CertTop_unary_max
import Theorems.Thm_ClauseBound_Alg_CertTop_unary_size
import Theorems.Thm_ClauseBound_Alg_CertTop_varAt_polyT3
import Theorems.Thm_ClauseBound_Alg_CertTop_wF_polyT3
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
import Theorems.Thm_ClauseBound_TopN_Cert_PbN_unary
import Theorems.Thm_ClauseBound_TopN_Cert_UbN_unary
import Theorems.Thm_ClauseBound_TopN_Cert_betaN_unary
import Theorems.Thm_ClauseBound_TopN_Cert_blockN_unary
import Theorems.Thm_ClauseBound_TopN_Cert_layersN_unary
import Theorems.Thm_ClauseBound_TopN_Cert_root17_polyT
import Theorems.Thm_ClauseBound_TopN_Cert_tauOf_polyT
import Theorems.Thm_CountKSatRate_Cert_bruteN_polyT
import Theorems.Thm_CountKSatRate_Cert_decU_pad_polyT
import Theorems.Thm_CountKSatRate_Cert_leafM_polyT
import Theorems.Thm_CountKSatRate_Cert_nK_unary
import Theorems.Thm_CountKSatRate_Cert_numC_polyT_aux
import Theorems.Thm_CountKSatRate_Cert_polyT_stepCU
import Theorems.Thm_CountKSatRate_stCertWalkS
import Theorems.Thm_CountKSat_stCertDecU
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
import Theorems.Thm_Groundwork_PolyT_congr
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
import Theorems.Thm_Groundwork_Prog_Count_linkB_polyT
import Theorems.Thm_Groundwork_Prog_Count_links_polyT
import Theorems.Thm_Groundwork_Prog_Count_litAt_polyT
import Theorems.Thm_Groundwork_Prog_Count_locals_polyT
import Theorems.Thm_Groundwork_Prog_Count_mu_polyT
import Theorems.Thm_Groundwork_Prog_Count_rows_polyT
import Theorems.Thm_Groundwork_Prog_Count_slotsOf_polyT
import Theorems.Thm_Groundwork_Prog_Count_varAt_polyT
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
import Theorems.Thm_Groundwork_Unary_of_length
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_Groundwork_block_polyT
import Theorems.Thm_Groundwork_digit_polyT
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
import Theorems.Thm_PaddedDescent_F_CertGrid_look_polyT
import Theorems.Thm_PaddedDescent_F_CertGrid_nRect_polyT
import Theorems.Thm_PaddedDescent_F_CertGrid_nRect_unary
import Theorems.Thm_PaddedDescent_F_CertGrid_priceCol_polyT
import Theorems.Thm_PaddedDescent_F_CertGrid_priceRow_polyT
import Theorems.Thm_PaddedDescent_F_CertGrid_sideCtx_polyT
import Theorems.Thm_PaddedDescent_F_CertNet_Pc2
import Theorems.Thm_PaddedDescent_F_CertNet_UcU
import Theorems.Thm_PaddedDescent_F_CertNet_betaC2
import Theorems.Thm_PaddedDescent_F_CertNet_betaCU
import Theorems.Thm_PaddedDescent_F_CertNet_capP
import Theorems.Thm_PaddedDescent_F_CertNet_capU
import Theorems.Thm_PaddedDescent_F_CertNet_col2
import Theorems.Thm_PaddedDescent_F_CertNet_goodB2
import Theorems.Thm_PaddedDescent_F_CertNet_isOne2
import Theorems.Thm_PaddedDescent_F_CertNet_isPsi2
import Theorems.Thm_PaddedDescent_F_CertNet_isW2
import Theorems.Thm_PaddedDescent_F_CertNet_lAt2
import Theorems.Thm_PaddedDescent_F_CertNet_labOf2
import Theorems.Thm_PaddedDescent_F_CertNet_lbLen2
import Theorems.Thm_PaddedDescent_F_CertNet_lbLens2
import Theorems.Thm_PaddedDescent_F_CertNet_look_polyT
import Theorems.Thm_PaddedDescent_F_CertNet_members2
import Theorems.Thm_PaddedDescent_F_CertNet_nLab2
import Theorems.Thm_PaddedDescent_F_CertNet_nP
import Theorems.Thm_PaddedDescent_F_CertNet_nStates2
import Theorems.Thm_PaddedDescent_F_CertNet_nU
import Theorems.Thm_PaddedDescent_F_CertNet_prs2
import Theorems.Thm_PaddedDescent_F_CertNet_qF2
import Theorems.Thm_PaddedDescent_F_CertNet_qP12
import Theorems.Thm_PaddedDescent_F_CertNet_qP22
import Theorems.Thm_PaddedDescent_F_CertNet_qW2
import Theorems.Thm_PaddedDescent_F_CertNet_rowSumU
import Theorems.Thm_PaddedDescent_F_CertNet_stLenU
import Theorems.Thm_PaddedDescent_F_CertNet_stLens2
import Theorems.Thm_PaddedDescent_F_CertNet_validB2
import Theorems.Thm_PaddedDescent_F_CertNet_zA2
import Theorems.Thm_PaddedDescent_F_CertNet_zAt2
import Theorems.Thm_PaddedDescent_F_CertNet_zOf2
import Theorems.Thm_PaddedDescent_F_CertSide_botF2
import Theorems.Thm_PaddedDescent_F_CertSide_c2P
import Theorems.Thm_PaddedDescent_F_CertSide_c2U
import Theorems.Thm_PaddedDescent_F_CertSide_cutF2
import Theorems.Thm_PaddedDescent_F_CertSide_he2
import Theorems.Thm_PaddedDescent_F_CertSide_itemF2
import Theorems.Thm_PaddedDescent_F_CertSide_look2
import Theorems.Thm_PaddedDescent_F_CertSide_node2
import Theorems.Thm_PaddedDescent_F_CertSide_rectDig2
import Theorems.Thm_PaddedDescent_F_CertSide_rectIx2
import Theorems.Thm_PaddedDescent_F_CertSide_rectLen2
import Theorems.Thm_PaddedDescent_F_CertSide_sideChk2
import Theorems.Thm_PaddedDescent_F_CertSide_sideChunk2
import Theorems.Thm_PaddedDescent_F_CertSide_sideEdges2
import Theorems.Thm_PaddedDescent_F_CertSide_sideLabels2
import Theorems.Thm_PaddedDescent_F_CertTop_betaOf_unary
import Theorems.Thm_PaddedDescent_F_CertTop_capOf_unary
import Theorems.Thm_PaddedDescent_F_CertTop_depthOf_unary
import Theorems.Thm_PaddedDescent_F_CertTop_gU_polyT
import Theorems.Thm_PaddedDescent_F_CertTop_layersOf_unary
import Theorems.Thm_PaddedDescent_F_CertTop_mulU_polyT
import Theorems.Thm_PaddedDescent_F_CertTop_polyT_pickKU
import Theorems.Thm_PaddedDescent_F_CertTop_polyT_stepKU
import Theorems.Thm_PaddedDescent_F_CertTop_polyT_theta
import Theorems.Thm_PaddedDescent_F_CertTop_sOf_polyT
import Theorems.Thm_PaddedDescent_F_CertTop_sOf_unary
import Theorems.Thm_PaddedDescent_F_CertTop_sqU_polyT
import Theorems.Thm_PaddedDescent_F_CertTop_tauOf_unary
import Theorems.Thm_PaddedDescent_F_CertTop_two_pow_betaOf_unary
import Theorems.Thm_PaddedDescent_F_Mark_Cert_adm_polyT
import Theorems.Thm_PaddedDescent_F_Mark_Cert_clAt_polyT
import Theorems.Thm_PaddedDescent_F_Mark_Cert_cls_polyT
import Theorems.Thm_PaddedDescent_F_Mark_Cert_enc_polyT
import Theorems.Thm_PaddedDescent_F_Mark_Cert_linkB_polyT
import Theorems.Thm_PaddedDescent_F_Mark_Cert_mW1_polyT
import Theorems.Thm_PaddedDescent_F_Mark_Cert_mW2_polyT
import Theorems.Thm_PaddedDescent_F_Mark_Cert_mW2l_polyT
import Theorems.Thm_PaddedDescent_F_Mark_Cert_mW3_polyT
import Theorems.Thm_PaddedDescent_F_Mark_Cert_mW4_polyT
import Theorems.Thm_PaddedDescent_F_Mark_Cert_mW_polyT
import Theorems.Thm_PaddedDescent_F_Mark_Cert_mWs_polyT
import Theorems.Thm_PaddedDescent_F_Mark_Cert_mark_polyT
import Theorems.Thm_PaddedDescent_F_Mark_Cert_mcap_unary
import Theorems.Thm_PaddedDescent_F_Mark_Cert_mlab_polyT
import Theorems.Thm_PaddedDescent_F_Mark_Cert_mu_polyT
import Theorems.Thm_PaddedDescent_F_Mark_Cert_mu_unary
import Theorems.Thm_PaddedDescent_F_Mark_Cert_ownB_polyT
import Theorems.Thm_PaddedDescent_F_Mark_Cert_qv_polyT
import Theorems.Thm_PaddedDescent_F_Mark_Cert_qv_unary
import Theorems.Thm_PaddedDescent_F_Mark_Cert_sign_polyT
import Theorems.Thm_PaddedDescent_F_Mark_Cert_str_polyT
import Theorems.Thm_PaddedDescent_F_Mark_Cert_tchB_polyT
import Theorems.Thm_PaddedDescent_F_Mark_Cert_tch_polyT
import Theorems.Thm_PaddedDescent_F_Mark_Cert_tst_polyT
import Theorems.Thm_PaddedDescent_F_cap_polyT
import Theorems.Thm_WidthK_Prog_polyT_heartsP
import Theorems.Thm_WidthK_Prog_polyT_maskP
import Theorems.Thm_WidthK_Prog_polyT_pickK
import Theorems.Thm_WidthK_Prog_polyT_stepK
import Theorems.Thm_WidthK_Prog_polyT_tryT
attribute [local fun_prop] ClauseBound.Alg.CertCount.mu_polyT2
attribute [local fun_prop] ClauseBound.Alg.CertCount.mu_unary2
attribute [local fun_prop] ClauseBound.Alg.CertCount.rows_polyT2
attribute [local fun_prop] ClauseBound.Alg.CertTop.PtopK_unary
attribute [local fun_prop] ClauseBound.Alg.CertTop.capF_unary3
attribute [local fun_prop] ClauseBound.Alg.CertTop.fF_polyT3
attribute [local fun_prop] ClauseBound.Alg.CertTop.lamTopK_unary
attribute [local fun_prop] ClauseBound.Alg.CertTop.linkB_polyT3
attribute [local fun_prop] ClauseBound.Alg.CertTop.links_polyT3
attribute [local fun_prop] ClauseBound.Alg.CertTop.litAt_polyT3
attribute [local fun_prop] ClauseBound.Alg.CertTop.locals_polyT3
attribute [local fun_prop] ClauseBound.Alg.CertTop.root9_polyT
attribute [local fun_prop] ClauseBound.Alg.CertTop.slotsOf_polyT3
attribute [local fun_prop] ClauseBound.Alg.CertTop.unary_max
attribute [local fun_prop] ClauseBound.Alg.CertTop.unary_size
attribute [local fun_prop] ClauseBound.Alg.CertTop.varAt_polyT3
attribute [local fun_prop] ClauseBound.Alg.CertTop.wF_polyT3
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
attribute [local fun_prop] ClauseBound.TopN.Cert.PbN_unary
attribute [local fun_prop] ClauseBound.TopN.Cert.UbN_unary
attribute [local fun_prop] ClauseBound.TopN.Cert.betaN_unary
attribute [local fun_prop] ClauseBound.TopN.Cert.blockN_unary
attribute [local fun_prop] ClauseBound.TopN.Cert.layersN_unary
attribute [local fun_prop] ClauseBound.TopN.Cert.root17_polyT
attribute [local fun_prop] CountKSatRate.Cert.polyT_stepCU
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
attribute [local fun_prop] Groundwork.Prog.Count.linkB_polyT
attribute [local fun_prop] Groundwork.Prog.Count.links_polyT
attribute [local fun_prop] Groundwork.Prog.Count.litAt_polyT
attribute [local fun_prop] Groundwork.Prog.Count.locals_polyT
attribute [local fun_prop] Groundwork.Prog.Count.mu_polyT
attribute [local fun_prop] Groundwork.Prog.Count.rows_polyT
attribute [local fun_prop] Groundwork.Prog.Count.slotsOf_polyT
attribute [local fun_prop] Groundwork.Prog.Count.varAt_polyT
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
attribute [local fun_prop] Groundwork.digit_polyT
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
attribute [local fun_prop] PaddedDescent.F.CertGrid.look_polyT
attribute [local fun_prop] PaddedDescent.F.CertGrid.nRect_polyT
attribute [local fun_prop] PaddedDescent.F.CertGrid.nRect_unary
attribute [local fun_prop] PaddedDescent.F.CertGrid.priceCol_polyT
attribute [local fun_prop] PaddedDescent.F.CertGrid.priceRow_polyT
attribute [local fun_prop] PaddedDescent.F.CertGrid.sideCtx_polyT
attribute [local fun_prop] PaddedDescent.F.CertNet.Pc2
attribute [local fun_prop] PaddedDescent.F.CertNet.UcU
attribute [local fun_prop] PaddedDescent.F.CertNet.betaC2
attribute [local fun_prop] PaddedDescent.F.CertNet.betaCU
attribute [local fun_prop] PaddedDescent.F.CertNet.capP
attribute [local fun_prop] PaddedDescent.F.CertNet.capU
attribute [local fun_prop] PaddedDescent.F.CertNet.col2
attribute [local fun_prop] PaddedDescent.F.CertNet.goodB2
attribute [local fun_prop] PaddedDescent.F.CertNet.isOne2
attribute [local fun_prop] PaddedDescent.F.CertNet.isPsi2
attribute [local fun_prop] PaddedDescent.F.CertNet.isW2
attribute [local fun_prop] PaddedDescent.F.CertNet.lAt2
attribute [local fun_prop] PaddedDescent.F.CertNet.labOf2
attribute [local fun_prop] PaddedDescent.F.CertNet.lbLen2
attribute [local fun_prop] PaddedDescent.F.CertNet.lbLens2
attribute [local fun_prop] PaddedDescent.F.CertNet.look_polyT
attribute [local fun_prop] PaddedDescent.F.CertNet.members2
attribute [local fun_prop] PaddedDescent.F.CertNet.nLab2
attribute [local fun_prop] PaddedDescent.F.CertNet.nP
attribute [local fun_prop] PaddedDescent.F.CertNet.nStates2
attribute [local fun_prop] PaddedDescent.F.CertNet.nU
attribute [local fun_prop] PaddedDescent.F.CertNet.prs2
attribute [local fun_prop] PaddedDescent.F.CertNet.qF2
attribute [local fun_prop] PaddedDescent.F.CertNet.qP12
attribute [local fun_prop] PaddedDescent.F.CertNet.qP22
attribute [local fun_prop] PaddedDescent.F.CertNet.qW2
attribute [local fun_prop] PaddedDescent.F.CertNet.rowSumU
attribute [local fun_prop] PaddedDescent.F.CertNet.stLenU
attribute [local fun_prop] PaddedDescent.F.CertNet.stLens2
attribute [local fun_prop] PaddedDescent.F.CertNet.validB2
attribute [local fun_prop] PaddedDescent.F.CertNet.zA2
attribute [local fun_prop] PaddedDescent.F.CertNet.zAt2
attribute [local fun_prop] PaddedDescent.F.CertNet.zOf2
attribute [local fun_prop] PaddedDescent.F.CertSide.botF2
attribute [local fun_prop] PaddedDescent.F.CertSide.c2P
attribute [local fun_prop] PaddedDescent.F.CertSide.c2U
attribute [local fun_prop] PaddedDescent.F.CertSide.cutF2
attribute [local fun_prop] PaddedDescent.F.CertSide.he2
attribute [local fun_prop] PaddedDescent.F.CertSide.itemF2
attribute [local fun_prop] PaddedDescent.F.CertSide.look2
attribute [local fun_prop] PaddedDescent.F.CertSide.node2
attribute [local fun_prop] PaddedDescent.F.CertSide.rectDig2
attribute [local fun_prop] PaddedDescent.F.CertSide.rectIx2
attribute [local fun_prop] PaddedDescent.F.CertSide.rectLen2
attribute [local fun_prop] PaddedDescent.F.CertSide.sideChk2
attribute [local fun_prop] PaddedDescent.F.CertSide.sideChunk2
attribute [local fun_prop] PaddedDescent.F.CertSide.sideEdges2
attribute [local fun_prop] PaddedDescent.F.CertSide.sideLabels2
attribute [local fun_prop] PaddedDescent.F.CertTop.betaOf_unary
attribute [local fun_prop] PaddedDescent.F.CertTop.capOf_unary
attribute [local fun_prop] PaddedDescent.F.CertTop.depthOf_unary
attribute [local fun_prop] PaddedDescent.F.CertTop.gU_polyT
attribute [local fun_prop] PaddedDescent.F.CertTop.layersOf_unary
attribute [local fun_prop] PaddedDescent.F.CertTop.mulU_polyT
attribute [local fun_prop] PaddedDescent.F.CertTop.polyT_pickKU
attribute [local fun_prop] PaddedDescent.F.CertTop.polyT_stepKU
attribute [local fun_prop] PaddedDescent.F.CertTop.polyT_theta
attribute [local fun_prop] PaddedDescent.F.CertTop.sOf_polyT
attribute [local fun_prop] PaddedDescent.F.CertTop.sOf_unary
attribute [local fun_prop] PaddedDescent.F.CertTop.sqU_polyT
attribute [local fun_prop] PaddedDescent.F.CertTop.tauOf_unary
attribute [local fun_prop] PaddedDescent.F.CertTop.two_pow_betaOf_unary
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.adm_polyT
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.clAt_polyT
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.cls_polyT
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.enc_polyT
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.linkB_polyT
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.mW1_polyT
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.mW2_polyT
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.mW2l_polyT
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.mW3_polyT
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.mW4_polyT
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.mW_polyT
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.mWs_polyT
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.mark_polyT
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.mcap_unary
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.mlab_polyT
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.mu_polyT
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.mu_unary
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.ownB_polyT
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.qv_polyT
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.qv_unary
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.sign_polyT
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.str_polyT
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.tchB_polyT
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.tch_polyT
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.tst_polyT
attribute [local fun_prop] PaddedDescent.F.cap_polyT
attribute [local fun_prop] WidthK.Prog.polyT_heartsP
attribute [local fun_prop] WidthK.Prog.polyT_maskP
attribute [local fun_prop] WidthK.Prog.polyT_pickK
attribute [local fun_prop] WidthK.Prog.polyT_stepK
attribute [local fun_prop] WidthK.Prog.polyT_tryT
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
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertTopOL
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertTopOL
theorem _root_.solution (hC : StCertCountOL) : StCertO := by
  intro Idx _ S hP c n₀ k pick slU hpick hsl
  have hd0 : PolyT (decU k) := stCertDecU k
  have hn0 : Unary (nK k) := Unary.of_length hd0.fst
  have hlv0 : PolyT fun x : List Bool => pick (root17 (nK k x)) := PolyT.comp hpick (root17_polyT hn0)
  have hi0 : PolyT (idxN k pick) := hlv0.snd
  have hs0 : Unary (precN k pick slU) := Unary.of_length (PolyT.comp hsl hlv0.fst)
  have hpl : PolyT (planO S c n₀ k pick slU) := planAtO_polyT S hP c n₀ k hn0 hi0 hs0
  constructor
  · have hd := decU_pad_polyT k
    have hn := nK_unary k
    have hp : PolyT fun p : List Bool × U => p.2 := by fun_prop
    have hs : Unary fun p : List Bool × U => precN k pick slU p.1 := hs0.comp PolyT.id'.fst
    have hl := leafM_polyT
    have hn1 : Unary fun q : (List Bool × U) × CNode => nK k q.1.1 := hn.comp (h := fun q : (List Bool × U) × CNode => q.1) (by fun_prop)
    have hs1 : Unary fun q : (List Bool × U) × CNode => precN k pick slU q.1.1 := hs.comp (h := fun q : (List Bool × U) × CNode => q.1) (by fun_prop)
    have hD1 := blockN_unary k hn1 hs1
    have hi1 : PolyT fun q : (List Bool × U) × CNode => idxN k pick q.1.1 := PolyT.comp (g := fun q : (List Bool × U) × CNode => q.1.1) hi0 (by fun_prop)
    have hv : PolyT fun q : (List Bool × U) × CNode => valO S k q.1.2 (idxN k pick q.1.1) (nK k q.1.1) (precN k pick slU q.1.1) q.2 := by
      have hg : PolyT fun q : (List Bool × U) × CNode => (q.1.2, idxN k pick q.1.1,
          (List.replicate (nK k q.1.1) (), List.replicate (blockN k (nK k q.1.1) (precN k pick slU q.1.1)) ()), leafM q.2) :=
        PolyT.prodMk (by fun_prop) (PolyT.prodMk hi1 (PolyT.prodMk (PolyT.prodMk hn1 hD1) (by fun_prop)))
      refine (PolyT.comp (hC Idx S hP k) hg).congr fun q => ?_
      simp only [List.length_replicate]
      rfl
    have hnum : PolyT fun p : List Bool × U => numOL S k (idxN k pick p.1) (precN k pick slU p.1) p := by
      have h := numC_polyT_aux stCertWalkS k (d := fun p : List Bool × U => decU k p.1) (pad := fun p => p.2)
        (τ := fun p => tauOf (precN k pick slU p.1)) (val := fun p => valO S k p.2 (idxN k pick p.1) (nK k p.1) (precN k pick slU p.1)) hd hp (tauOf_polyT hs) hv
      unfold numOL
      exact h
    have hno : PolyT fun p : List Bool × U => (planO S c n₀ k pick slU p.1).isNone := PolyT.optionIsNone (PolyT.comp hpl PolyT.id'.fst)
    unfold AO
    exact PolyT.comp outW_polyT (PolyT.prodMk hd (PolyT.cond' hno (bruteN_polyT k) hnum))
  · unfold eO
    exact PolyT.optionGetD hpl hn0.poly
end ClauseBound.ParityChecks.CertTopOL
