-- Prove2me | solution 1 for ClauseBound.TopN.Cert.UbN_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:58:57.303948+00:00
-- url     : https://prove2.me/submissions/b265e7ca-0773-4047-9010-d7414cb813dd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_ClauseBound_Alg_CertTop
import Definitions.Def_CountKSatRate_Cert
import Definitions.Def_PaddedDescent_F_CertEval
import Definitions.Def_ClauseBound_TopN_Cert
import Theorems.Thm_ClauseBound_TopN_Cert_betaN_unary
import Theorems.Thm_ClauseBound_TopN_Cert_layersN_unary
import Theorems.Thm_ClauseBound_TopN_Cert_blockN_unary
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
import Theorems.Thm_CountKSatRate_Cert_polyT_stepCU
import Theorems.Thm_Groundwork_DecodeK_clauseDec_polyT
import Theorems.Thm_Groundwork_Decode_clauseDec_polyT
import Theorems.Thm_Groundwork_Decode_slotDec_polyT
import Theorems.Thm_Groundwork_Decode_width_polyT
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
import Theorems.Thm_Groundwork_block_polyT
import Theorems.Thm_Groundwork_digit_polyT
import Theorems.Thm_Groundwork_query0_polyT
import Theorems.Thm_Groundwork_tri_polyT
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


attribute [local fun_prop] ClauseBound.TopN.Cert.betaN_unary
attribute [local fun_prop] ClauseBound.TopN.Cert.layersN_unary
attribute [local fun_prop] ClauseBound.TopN.Cert.blockN_unary

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.TopN ClauseBound.TopN.Cert
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open PaddedDescent.F.Mark (MCtx Cl cls nProf adm markF placeE)
variable {α : Type} [Enc α]
variable {K n s : α → ℕ}
namespace ClauseBound.TopN.Cert
theorem _root_.solution (k : ℕ) (hK : Unary K) (hn : Unary n) (hs : Unary s) : Unary fun x => UbN k (K x) (n x) (s x) := by
  have h1 := betaN_unary k hs
  have h2 := layersN_unary k hs
  unfold UbN Ub; fun_prop
end ClauseBound.TopN.Cert
