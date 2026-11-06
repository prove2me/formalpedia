-- Prove2me | solution 1 for CircuitLowerBound.TabF.clauseAt_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:49:35.626078+00:00
-- url     : https://prove2.me/submissions/3c3da26c-b1bb-481a-b1a0-63ff74c0314b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Cert_Sched
import Definitions.Def_CircuitLowerBound_Small
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Cert_TabF
import Theorems.Thm_CircuitLowerBound_TabF_bq_unary
import Theorems.Thm_CircuitLowerBound_TabF_litAt_polyT
import Theorems.Thm_CircuitLowerBound_Sched_bt_unary
import Theorems.Thm_CircuitLowerBound_Sched_tab_polyT
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
import Theorems.Thm_Groundwork_PolyT_two_pow
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_const
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



set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.TabF
open ENP Groundwork Sched
variable {α : Type} [Enc α]
variable {e : α → MCode} {L P : α → ℕ} (he : PolyT e) (hk : Unary fun x => kb (e x)) (hl : Unary fun x => lam (e x)) (hL : Unary L) (hP : PolyT P)
include he hk hl hL
include hP
namespace CircuitLowerBound.TabF
theorem _root_.solution {j : α → ℕ} (hj : PolyT j) : PolyT fun x => clauseAt (e x) (L x) (P x) (j x) := by
  have p1 : PolyT fun x => 2 ^ bq (e x) (L x) := PolyT.two_pow (bq_unary he hl hL)
  have p2 : PolyT fun x => 2 ^ bt (e x) (L x) := PolyT.two_pow (bt_unary he hL)
  have p3 : PolyT fun x => 2 ^ (bt (e x) (L x) + bq (e x) (L x)) := PolyT.two_pow ((bt_unary he hL).add (bq_unary he hl hL))
  have ht : PolyT fun x => j x / 2 ^ bq (e x) (L x) % 2 ^ bt (e x) (L x) := PolyT.mod (PolyT.div hj p1) p2
  have hq : PolyT fun x => j x % 2 ^ bq (e x) (L x) := PolyT.mod hj p1
  have hc : PolyT fun x => (tab (e x)).getD (j x / 2 ^ (bt (e x) (L x) + bq (e x) (L x))) zeroCl :=
    PolyT.getD (tab_polyT he) (PolyT.div hj p3) (PolyT.const _)
  have a1 := litAt_polyT he hk hl hL hP ht hq (l := fun x => ((tab (e x)).getD (j x / 2 ^ (bt (e x) (L x) + bq (e x) (L x))) zeroCl).1) hc.fst
  have a2 := litAt_polyT he hk hl hL hP ht hq (l := fun x => ((tab (e x)).getD (j x / 2 ^ (bt (e x) (L x) + bq (e x) (L x))) zeroCl).2.1) hc.snd.fst
  have a3 := litAt_polyT he hk hl hL hP ht hq (l := fun x => ((tab (e x)).getD (j x / 2 ^ (bt (e x) (L x) + bq (e x) (L x))) zeroCl).2.2) hc.snd.snd
  have key : ∀ a b c : α → ℕ × Bool, PolyT a → PolyT b → PolyT c → PolyT fun x => [a x, b x, c x] := by
    intro a b c _ _ _
    fun_prop
  exact key _ _ _ a1 a2 a3
end CircuitLowerBound.TabF
