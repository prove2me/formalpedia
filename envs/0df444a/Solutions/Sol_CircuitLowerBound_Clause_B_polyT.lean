-- Prove2me | solution 1 for CircuitLowerBound.Clause.B_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:22:32.203773+00:00
-- url     : https://prove2.me/submissions/b6700a40-ab3d-4009-b450-8d4d6d24925c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Clause
import Theorems.Thm_CircuitLowerBound_Clause_prevW_polyT
import Theorems.Thm_CircuitLowerBound_Clause_litI_polyT
import Theorems.Thm_CircuitLowerBound_Clause_fbit_polyT
import Theorems.Thm_CircuitLowerBound_Clause_Ew_polyT
import Theorems.Thm_CircuitLowerBound_Clause_selGate_polyT
import Theorems.Thm_CircuitLowerBound_Clause_Fw_polyT
import Theorems.Thm_CircuitLowerBound_Clause_fldGate_polyT
import Theorems.Thm_CircuitLowerBound_Clause_cinT_polyT
import Theorems.Thm_CircuitLowerBound_Clause_cinQ_polyT
import Theorems.Thm_CircuitLowerBound_Clause_timeBit_polyT
import Theorems.Thm_CircuitLowerBound_Clause_dWire_polyT
import Theorems.Thm_CircuitLowerBound_Clause_szL_polyT
import Theorems.Thm_CircuitLowerBound_Clause_offA_polyT
import Theorems.Thm_CircuitLowerBound_Clause_coreB_polyT
import Theorems.Thm_CircuitLowerBound_Clause_kb_polyT
import Theorems.Thm_CircuitLowerBound_Clause_lam_polyT
import Theorems.Thm_CircuitLowerBound_Clause_tab_polyT
import Theorems.Thm_CircuitLowerBound_Clause_bt_polyT
import Theorems.Thm_CircuitLowerBound_Clause_bq_polyT
import Theorems.Thm_CircuitLowerBound_Clause_size_aux
import Theorems.Thm_CircuitLowerBound_Clause_rb_polyT
import Theorems.Thm_CircuitLowerBound_Clause_nb_polyT
import Theorems.Thm_CircuitLowerBound_Clause_dSum_polyT
import Theorems.Thm_Groundwork_Decode_clauseDec_polyT
import Theorems.Thm_Groundwork_Decode_slotDec_polyT
import Theorems.Thm_Groundwork_Decode_width_polyT
import Theorems.Thm_Groundwork_PB_add
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
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_of_le
import Theorems.Thm_Groundwork_Unary_of_length
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_Groundwork_block_polyT
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
attribute [local fun_prop] Groundwork.Decode.clauseDec_polyT
attribute [local fun_prop] Groundwork.Decode.slotDec_polyT
attribute [local fun_prop] Groundwork.Decode.width_polyT
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


attribute [local fun_prop] CircuitLowerBound.Clause.prevW_polyT
attribute [local fun_prop] CircuitLowerBound.Clause.litI_polyT
attribute [local fun_prop] CircuitLowerBound.Clause.fbit_polyT
attribute [local fun_prop] CircuitLowerBound.Clause.Ew_polyT
attribute [local fun_prop] CircuitLowerBound.Clause.selGate_polyT
attribute [local fun_prop] CircuitLowerBound.Clause.Fw_polyT
attribute [local fun_prop] CircuitLowerBound.Clause.fldGate_polyT
attribute [local fun_prop] CircuitLowerBound.Clause.cinT_polyT
attribute [local fun_prop] CircuitLowerBound.Clause.cinQ_polyT
attribute [local fun_prop] CircuitLowerBound.Clause.timeBit_polyT
attribute [local fun_prop] CircuitLowerBound.Clause.dWire_polyT
attribute [local fun_prop] CircuitLowerBound.Clause.szL_polyT
attribute [local fun_prop] CircuitLowerBound.Clause.offA_polyT
attribute [local fun_prop] CircuitLowerBound.Clause.kb_polyT
attribute [local fun_prop] CircuitLowerBound.Clause.lam_polyT
attribute [local fun_prop] CircuitLowerBound.Clause.tab_polyT
attribute [local fun_prop] CircuitLowerBound.Clause.bt_polyT
attribute [local fun_prop] CircuitLowerBound.Clause.bq_polyT
attribute [local fun_prop] CircuitLowerBound.Clause.rb_polyT
attribute [local fun_prop] CircuitLowerBound.Clause.nb_polyT
attribute [local fun_prop] CircuitLowerBound.Clause.dSum_polyT

set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Clause
open ENP Groundwork CircuitLowerBound.Blocks
variable {α : Type} [Enc α]
namespace CircuitLowerBound.Clause
theorem _root_.solution : PolyT B := by
  have hL : Unary fun x : MCode × List Unit × ℕ => x.2.1.length := Unary.of_length (by fun_prop)
  have hl := hL.poly
  have hbq : Unary fun x : MCode × List Unit × ℕ => min (bq x.1 x.2.1.length) x.2.1.length := Unary.of_le hL (by fun_prop) fun x => min_le_right _ _
  have hbt : Unary fun x : MCode × List Unit × ℕ => bt x.1 x.2.1.length :=
    Unary.of_le hL (by fun_prop) fun x => by
      unfold bt
      exact (Nat.div_le_self _ _).trans (by omega)
  have hrb : Unary fun x : MCode × List Unit × ℕ => rb x.1 :=
    Unary.of_le (Unary.of_length (w := fun x : MCode × List Unit × ℕ => tab x.1) (by fun_prop)) (by fun_prop) fun x => Nat.size_le.2 Nat.lt_two_pow_self
  have hkb : Unary fun x : MCode × List Unit × ℕ => min (kb x.1) x.2.1.length := Unary.of_le hL (by fun_prop) fun x => min_le_right _ _
  have hs : PolyT fun x : MCode × List Unit × ℕ => Nat.size (dSum (tab x.1)) := size_aux (by fun_prop)
  have hq := hbq.poly
  have hDq : Unary fun x : MCode × List Unit × ℕ => min (Nat.size (dSum (tab x.1))) (min (bq x.1 x.2.1.length) x.2.1.length + 1) :=
    Unary.of_le (hbq.add (Unary.const 1)) (by fun_prop) fun x => min_le_right _ _
  exact coreB_polyT (by fun_prop) hbq hbt hrb hkb hDq hL (by fun_prop) (by fun_prop)
end CircuitLowerBound.Clause
