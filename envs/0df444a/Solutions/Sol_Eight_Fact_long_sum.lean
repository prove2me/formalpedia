-- Prove2me | solution 1 for Eight.Fact.long_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:22:07.2509+00:00
-- url     : https://prove2.me/submissions/ebc6c76b-9cae-4845-9f0a-4e02ce2db2cc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_FactDefs
import Definitions.Def_Eight_SecCrossing_Blocks
import Definitions.Def_Eight_SecCrossing_Chunk
import Definitions.Def_Eight_SecCrossing_MulOut
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Fact
import Theorems.Thm_Eight_Fact_sum_words_count
import Theorems.Thm_Eight_Fact_fTop_long
import Theorems.Thm_Eight_Fact_fBot_long
import Theorems.Thm_Eight_Fact_lenW_eq
import Theorems.Thm_Eight_sum_words_add
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
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
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.length
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
open Eight
open Groundwork Groundwork.Prog PaddedDescent.F Finset
open Eight.Fact
namespace Eight.Fact
theorem _root_.solution (hC : StChunk) {tr : Bool} {lam i : ℕ} (hi : i ≤ tOf lam) {a b a' b' : List Bool} (ha : a.length = lam) (ha' : a'.length = lam)
    (hL : useLong tr lam i = true) :
    ∑ θ ∈ words (longCap tr (tOf lam) i), fTop (tr, i, a, b, θ) * fBot (tr, i, a', b', θ) =
      ∑ S ∈ (range (tOf lam)).powersetCard i, ∏ s ∈ range (tOf lam),
        if (decide (s ∈ S) != tr) = true then Rb (blkL a s) (blkL a' s) (blkL b s) (blkL b' s) else Rb (blkL a s) (blkL b s) (blkL a' s) (blkL b' s) := by
  have hcap : longCap tr (tOf lam) i = tOf lam + (3 * tOf lam + 3 * (bif tr then tOf lam - i else i)) := by
    cases tr <;> simp [longCap] <;> omega
  rw [hcap, sum_words_add, ← sum_words_count (tOf lam) i fun s β =>
    if (β != tr) = true then Rb (blkL a s) (blkL a' s) (blkL b s) (blkL b' s) else Rb (blkL a s) (blkL b s) (blkL a' s) (blkL b' s)]
  refine sum_congr rfl fun Q hQ => ?_
  have hQ := mem_words.1 hQ
  have e1 : ∀ w, fTop (tr, i, a, b, Q ++ w) = if Q.count true = i then prodL (tOf lam) (topAt tr Q w a b) else 0 := fun w => by
    subst ha; exact fTop_long hL hQ
  have e2 : ∀ w, fBot (tr, i, a', b', Q ++ w) = if Q.count true = i then prodL (tOf lam) (botAt tr Q w a' b') else 0 := fun w => by
    subst ha'; exact fBot_long hL hQ
  by_cases hc : Q.count true = i
  · rw [if_pos hc, ← lenW_eq hQ hc]
    refine Eq.trans (sum_congr rfl fun w _ => ?_) (hC tr (tOf lam) Q a b a' b')
    rw [e1, e2, if_pos hc, if_pos hc]
  · rw [if_neg hc]
    refine sum_eq_zero fun w _ => ?_
    rw [e1, if_neg hc, zero_mul]
end Eight.Fact
