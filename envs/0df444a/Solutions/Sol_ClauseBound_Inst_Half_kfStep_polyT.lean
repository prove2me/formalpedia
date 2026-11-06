-- Prove2me | solution 1 for ClauseBound.Inst.Half.kfStep_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:36:20.954901+00:00
-- url     : https://prove2.me/submissions/7a0b0876-52ad-4318-aae3-a0d87bc5742e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTab
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Inst_CertHalfTab
import Theorems.Thm_ClauseBound_Inst_Half_erase_polyT
import Theorems.Thm_ClauseBound_Inst_Half_count_unary
import Theorems.Thm_ClauseBound_Inst_Half_betF_polyT
import Theorems.Thm_ClauseBound_Inst_Half_tab_polyT
import Theorems.Thm_ClauseBound_Inst_Half_lookT_polyT
import Theorems.Thm_ClauseBound_Inst_Half_nopE_polyT
import Theorems.Thm_ClauseBound_Inst_Half_oneT_polyT
import Theorems.Thm_ClauseBound_Inst_Half_tabOp_polyT
import Theorems.Thm_ClauseBound_Inst_Half_kfInit_polyT
import Theorems.Thm_ClauseBound_Inst_Half_kfEntry_polyT
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


attribute [local fun_prop] ClauseBound.Inst.Half.erase_polyT
attribute [local fun_prop] ClauseBound.Inst.Half.count_unary
attribute [local fun_prop] ClauseBound.Inst.Half.betF_polyT
attribute [local fun_prop] ClauseBound.Inst.Half.lookT_polyT
attribute [local fun_prop] ClauseBound.Inst.Half.nopE_polyT
attribute [local fun_prop] ClauseBound.Inst.Half.oneT_polyT
attribute [local fun_prop] ClauseBound.Inst.Half.tabOp_polyT
attribute [local fun_prop] ClauseBound.Inst.Half.kfInit_polyT

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Inst.Rec
variable {α : Type} [Enc α]
namespace ClauseBound.Inst.Half
theorem _root_.solution {W h n : α → ℕ} {flat : α → List (List ℕ)} {S : α → List (List ℤ)} (hW : Unary W) (hh : Unary h) (hn : PolyT n)
    (hf : PolyT flat) (hS : PolyT S) : PolyT fun x => kfStep (W x) (h x) (n x) (flat x) (S x) := by
  unfold kfStep
  refine PolyT.map (l := fun x => List.range (h x + 1)) ?_ (by fun_prop)
  refine tab_polyT (flat := fun p : α × ℕ => flat p.1) (f := fun p π σ => sumR (min (n p.1) (W p.1)) fun j =>
      if j + 1 ≤ p.2 then sgnZ ((n p.1 - 1 : ℕ) : ℤ) * chooseZ (n p.1 : ℤ) (j + 1) *
        nopE (W p.1) (j + 1) (flat p.1) ((S p.1).getD (p.2 - (j + 1)) []) π σ
      else 0) (by fun_prop) ?_
  exact kfEntry_polyT (α := (α × ℕ) × List ℕ × List ℕ) (W := fun q => W q.1.1) (n := fun q => n q.1.1) (w := fun q => q.1.2)
    (flat := fun q => flat q.1.1) (S := fun q => S q.1.1) (π := fun q => q.2.1) (σ := fun q => q.2.2)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
end ClauseBound.Inst.Half
