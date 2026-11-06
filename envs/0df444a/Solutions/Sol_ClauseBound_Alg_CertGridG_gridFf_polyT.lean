-- Prove2me | solution 1 for ClauseBound.Alg.CertGridG.gridFf_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:58:58.72728+00:00
-- url     : https://prove2.me/submissions/221db917-8b01-496c-a422-e49f389db313

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_PaddedDescent_F_CertGrid
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ToTuring_Poly_Words
import Definitions.Def_ClauseBound_Alg_CertGridG
import Theorems.Thm_ClauseBound_Alg_CertGridG_unary_ite
import Theorems.Thm_ClauseBound_Alg_CertGridG_unary_mod
import Theorems.Thm_ClauseBound_Alg_CertGridG_unary_max
import Theorems.Thm_ClauseBound_Alg_CertGridG_unary_min
import Theorems.Thm_ClauseBound_Alg_CertGridG_unary_min_right
import Theorems.Thm_ClauseBound_Alg_CertGridG_c2_unary
import Theorems.Thm_ClauseBound_Alg_CertGridG_c2_polyT
import Theorems.Thm_ClauseBound_Alg_CertGridG_tri_unary
import Theorems.Thm_ClauseBound_Alg_CertGridG_prodL_polyT_min
import Theorems.Thm_ClauseBound_Alg_CertGridG_nRectG_unary
import Theorems.Thm_ClauseBound_Alg_CertGridG_nRectG_polyT
import Theorems.Thm_ClauseBound_Alg_CertGridG_nParts_unary
import Theorems.Thm_ClauseBound_Alg_CertGridG_nMemb_unary
import Theorems.Thm_ClauseBound_Alg_CertGridG_nParts_polyT
import Theorems.Thm_ClauseBound_Alg_CertGridG_nMemb_polyT
import Theorems.Thm_ClauseBound_Alg_CertGridG_nodeG_polyT
import Theorems.Thm_ClauseBound_Alg_CertGridG_rectIxG_polyT
import Theorems.Thm_ClauseBound_Alg_CertGridG_heG_polyT
import Theorems.Thm_ClauseBound_Alg_CertGridG_chkG_polyT
import Theorems.Thm_ClauseBound_Alg_CertGridG_sqrt_polyT
import Theorems.Thm_ClauseBound_Alg_CertGridG_sqrt_unary
import Theorems.Thm_ClauseBound_Alg_CertGridG_K_unary
import Theorems.Thm_ClauseBound_Alg_CertGridG_p_unary
import Theorems.Thm_ClauseBound_Alg_CertGridG_d_unary
import Theorems.Thm_ClauseBound_Alg_CertGridG_D_unary__6c8f65
import Theorems.Thm_ClauseBound_Alg_CertGridG_h_unary
import Theorems.Thm_ClauseBound_Alg_CertGridG_a_unary
import Theorems.Thm_ClauseBound_Alg_CertGridG_b_unary
import Theorems.Thm_ClauseBound_Alg_CertGridG_thin_polyT
import Theorems.Thm_ClauseBound_Alg_CertGridG_Nof_unary
import Theorems.Thm_ClauseBound_Alg_CertGridG_itemG_polyT
import Theorems.Thm_Groundwork_PB_const
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
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_poly
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
import Theorems.Thm_PaddedDescent_F_cap_polyT
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
attribute [local fun_prop] PaddedDescent.F.cap_polyT


attribute [local fun_prop] ClauseBound.Alg.CertGridG.unary_ite
attribute [local fun_prop] ClauseBound.Alg.CertGridG.unary_mod
attribute [local fun_prop] ClauseBound.Alg.CertGridG.unary_max
attribute [local fun_prop] ClauseBound.Alg.CertGridG.unary_min
attribute [local fun_prop] ClauseBound.Alg.CertGridG.c2_unary
attribute [local fun_prop] ClauseBound.Alg.CertGridG.c2_polyT
attribute [local fun_prop] ClauseBound.Alg.CertGridG.tri_unary
attribute [local fun_prop] ClauseBound.Alg.CertGridG.nRectG_unary
attribute [local fun_prop] ClauseBound.Alg.CertGridG.nRectG_polyT
attribute [local fun_prop] ClauseBound.Alg.CertGridG.nParts_unary
attribute [local fun_prop] ClauseBound.Alg.CertGridG.nMemb_unary
attribute [local fun_prop] ClauseBound.Alg.CertGridG.nParts_polyT
attribute [local fun_prop] ClauseBound.Alg.CertGridG.nMemb_polyT
attribute [local fun_prop] ClauseBound.Alg.CertGridG.nodeG_polyT
attribute [local fun_prop] ClauseBound.Alg.CertGridG.rectIxG_polyT
attribute [local fun_prop] ClauseBound.Alg.CertGridG.heG_polyT
attribute [local fun_prop] ClauseBound.Alg.CertGridG.chkG_polyT
attribute [local fun_prop] ClauseBound.Alg.CertGridG.sqrt_polyT
attribute [local fun_prop] ClauseBound.Alg.CertGridG.sqrt_unary
attribute [local fun_prop] ClauseBound.Alg.CertGridG.K_unary
attribute [local fun_prop] ClauseBound.Alg.CertGridG.p_unary
attribute [local fun_prop] ClauseBound.Alg.CertGridG.d_unary
attribute [local fun_prop] ClauseBound.Alg.CertGridG.D_unary
attribute [local fun_prop] ClauseBound.Alg.CertGridG.h_unary
attribute [local fun_prop] ClauseBound.Alg.CertGridG.a_unary
attribute [local fun_prop] ClauseBound.Alg.CertGridG.b_unary
attribute [local fun_prop] ClauseBound.Alg.CertGridG.thin_polyT
attribute [local fun_prop] ClauseBound.Alg.CertGridG.Nof_unary

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertGridG
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α]
variable {P : PiecesF} (K : P.Keeps)
include K
namespace ClauseBound.Alg.CertGridG
theorem _root_.solution {pad : α → U} {p d h ℓ y : α → ℕ} {tr : α → Bool} {q : α → FQ} (hpad : PolyT pad) (hp : Unary p) (hd : Unary d) (ht : PolyT tr)
    (hh : Unary h) (hℓ : Unary ℓ) (hy : PolyT y) (hq : PolyT q) :
    PolyT fun x => gridFf P (pad x) (p x) (d x) (tr x) (h x) (ℓ x) (y x) (q x) := by
  have hp' := hp.poly
  have hd' := hd.poly
  have hℓ' := hℓ.poly
  have hmm : Unary fun x => nMemb (p x) (d x) (tr x) * nMemb (p x) (d x) (tr x) := by fun_prop
  have h1 : PolyT fun x => prodL (nMemb (p x) (d x) (tr x) * nMemb (p x) (d x) (tr x)) fun j =>
      if j / nMemb (p x) (d x) (tr x) < j % nMemb (p x) (d x) (tr x) then
        rectG P (pad x) (p x) (d x) (tr x) (h x) (ℓ x) (y x) (q x) (j / nMemb (p x) (d x) (tr x)) (j % nMemb (p x) (d x) (tr x)) else 1 :=
    prodL_polyT_min hmm (itemG_polyT K (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
      (unary_min_right (by fun_prop) (by fun_prop)))
  have h2 : PolyT fun x => (List.range (nMemb (p x) (d x) (tr x))).all fun i =>
      heG (p x) (d x) (ℓ x) (q x).2.1 i (nodeG (d x) (tr x) (q x).1.2 i) == block (ℓ x) i (q x).2.2 := by fun_prop
  exact PolyT.cond' h2 h1 (PolyT.const 0)
end ClauseBound.Alg.CertGridG
