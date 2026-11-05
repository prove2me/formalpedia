-- Prove2me | solution 1 for ClauseBound.Alg.TopVal.stCorrectM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:54:34.099197+00:00
-- url     : https://prove2.me/submissions/9930e7b8-53c2-4865-85fa-4c282c54e7e8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_PaddedDescent_F_RebalG
import Definitions.Def_CountKSat_Value
import Definitions.Def_CountKSat_InOut
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_CountKSatRate_Brute
import Definitions.Def_CountKSatRate_Brute
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_ClauseBound_Alg_TopVal
import Theorems.Thm_CountKSatRate_Brute_length_filter_satAt
import Theorems.Thm_CountKSatRate_Brute_outW_eq_binary
import Theorems.Thm_CountKSat_CountTop_numSat_of_nil
import Theorems.Thm_CountKSat_Value_value_wordNet_eq_cntN
import Theorems.Thm_CountKSat_stCntToN
import Theorems.Thm_Groundwork_Decode_length_toN
import Theorems.Thm_Groundwork_Decode_mem_toN
import Theorems.Thm_Groundwork_Decode_nil_mem_toN
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
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
import Theorems.Thm_Groundwork_TM_update_withIO
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
import Theorems.Thm_PaddedDescent_F_rng_eq
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
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


namespace ClauseBound.Alg.TopVal
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Prog.Count PaddedDescent PaddedDescent.F CountKSat
private theorem needTopC_eq {Idx : Type} [Enc Idx] {S : Solver Idx} (hP : S.Poly) {b : U} {i : Idx} {k m v : ℕ} (h : needTopC S b i k m = some v) :
    v = needTop S i k m := by
  unfold needTopC at h
  obtain ⟨w, hw, h⟩ := Option.bind_eq_some_iff.1 h
  obtain rfl := hP.needC_eq _ _ _ hw
  split_ifs at h
  exact (Option.some.inj h).symm
end ClauseBound.Alg.TopVal
set_option autoImplicit false
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.TopVal
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Prog.Count PaddedDescent PaddedDescent.F CountKSat
namespace ClauseBound.Alg.TopVal
theorem _root_.solution (hD : StDecM) (hC : StCountG) : StCorrectM := by
  intro Idx _ S e C₀ Q hP k n φ hk _ hφ hocc pad hpad
  obtain ⟨hkO, hdec⟩ := hD k n φ hk hφ.1
  simp only [eM, planM, hdec, hkO, List.length_replicate, Decode.length_toN] at hpad
  simp only [AM, planM, hdec, hkO, List.length_replicate, Decode.length_toN]
  rw [CountKSatRate.Brute.outW_eq_binary]
  congr 1
  rcases hm : needTopC S (List.replicate n ()) (Q.pick (root9 φ.length)).2 k φ.length with _ | v
  · rw [hm, Option.getD_none] at hpad
    rw [Option.isNone_none, cond_true, rng_eq hpad, CountKSatRate.Brute.length_filter_satAt]
  · rw [hm, Option.getD_some, needTopC_eq hP hm] at hpad
    rw [Option.isNone_some, cond_false]
    have hnilψ : hasNil (Decode.toN φ) = true ↔ [] ∈ φ := by
      rw [← Decode.nil_mem_toN]
      simp [hasNil, List.any_eq_true]
    by_cases hnil : [] ∈ φ
    · rw [hnilψ.2 hnil, cond_true, CountTop.numSat_of_nil hnil]
    · have hn' : hasNil (Decode.toN φ) = false := by
        rw [← Bool.not_eq_true]; exact fun h => hnil (hnilψ.1 h)
      rw [hn', cond_false]
      obtain ⟨i, hi⟩ : ∃ i, i = (Q.pick (root9 φ.length)).2 := ⟨_, rfl⟩
      rw [← hi] at hpad ⊢
      have hidx : i = Q.idx (Q.pick (root9 φ.length)).1.length := hi.trans (Q.pick_idx _)
      have hK : 2 ≤ S.K i := hidx ▸ Q.K_two _
      have hg : 0 < 3 * S.K i ^ 8 := by
        have : 0 < S.K i ^ 8 := Nat.pow_pos (by omega)
        omega
      have hw : ∀ C ∈ Decode.toN φ, C.length ≤ k := fun D hD' => by
        obtain ⟨⟨C, hC', hl⟩, -⟩ := Decode.mem_toN hD'
        exact hl ▸ hφ.1 C hC'
      rw [hC Idx S _ Q.correct pad i k (Decode.toN φ) ⟨_, hidx⟩ hK hk hw (by rw [Decode.length_toN]; exact hpad),
        Value.value_wordNet_eq_cntN hg hw (fun D hD' => (Decode.mem_toN hD').2) (fun v hv => ?_), Int.toNat_natCast, stCntToN n φ]
      obtain ⟨C, hC', l, hl, hlv⟩ := hocc ⟨v, hv⟩
      exact ⟨C.map fun l => (l.1.val, l.2), List.mem_map.2 ⟨C, hC', rfl⟩, (l.1.val, l.2), List.mem_map.2 ⟨l, hl, rfl⟩, by simp [hlv]⟩
end ClauseBound.Alg.TopVal
