-- Prove2me | solution 1 for ClauseBound.ParityChecks.Count.orcOK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:21:20.190992+00:00
-- url     : https://prove2.me/submissions/64f9b531-bf21-4792-adc4-6afa6ce351ad

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Run
import Definitions.Def_ClauseBound_ParityChecks_RunF
import Definitions.Def_PaddedDescent_F_Eval
import Definitions.Def_PaddedDescent_F_Eval
import Definitions.Def_ClauseBound_ParityChecks_Count
import Theorems.Thm_ClauseBound_ParityChecks_Count_Lof_pad
import Theorems.Thm_ClauseBound_ParityChecks_Count_incL_pad
import Theorems.Thm_ClauseBound_ParityChecks_Count_wfC_pad
import Theorems.Thm_ClauseBound_ParityChecks_Count_lam_subset
import Theorems.Thm_ClauseBound_ParityChecks_Count_tent_mono
import Theorems.Thm_ClauseBound_ParityChecks_Count_getD2
import Theorems.Thm_ClauseBound_ParityChecks_Count_getD3
import Theorems.Thm_ClauseBound_ParityChecks_Count_ev3
import Theorems.Thm_ClauseBound_ParityChecks_Count_ev2
import Theorems.Thm_ClauseBound_ParityChecks_Num_all_ok
import Theorems.Thm_ClauseBound_ParityChecks_div_congr
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_all
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
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length
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
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Count
open Finset Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Eval ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW _root_.ParityChecks
variable (hE : StEvW) (hSh : StShape) {Idx : Type} [Enc Idx] (S : Solver Idx) (ok : Idx → Prop) (hC : S.Correct ok) (k : ℕ) (pad : U) (i : Idx) (n Δ : ℕ) (ψ : Fml)
  (nb r i₀ β : ℕ) (hok : ok i) (hK : 2 ≤ S.K i) (hW : WfL k n [ψ]) (hocc : ∀ v, (occ ψ v).length ≤ Δ) (hmΔ : ψ.length ≤ Δ * n) (hnb : 2 ≤ nb)
  (hLD : n < 2 * (nb * LD Δ)) (hr : r ≤ 6 * n) (hcap : β - 1 + r ≤ 11 * n) (hFit : FitsOL S k i n Δ pad.length)
include hE hSh hC hok hK hW hocc hmΔ hnb hLD hr hcap hFit
namespace ClauseBound.ParityChecks.Count
theorem _root_.solution (hB : StBridgeB) (hA : StBridgeA) (hβ : 1 ≤ β) (hnbc : nb + 1 ≤ β - 1 + r) (hi₀ : i₀ ≤ β - 1 + r) :
    OrcOK (mkQ ψ nb r i₀ β) (Vof (n := n) ψ) (orcA S k pad i n Δ (mkQ ψ nb r i₀ β) ψ) (orcB S k pad i n Δ (mkQ ψ nb r i₀ β) ψ) := by
  intro Ls cur e hlt hLs hcur he hT
  have hlt' : Ls.length < r := hlt
  have hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n := fun C hC' => (hW ψ (by simp) C hC').2.2
  have hall : ∀ L ∈ Ls ++ [cur], ChkOK ψ.length L := Num.all_ok (q := mkQ ψ nb r i₀ β) hLs hcur he
  have hlen : (Ls ++ [cur]).length ≤ r := by rw [List.length_append, List.length_singleton]; omega
  have hWf := wfC_pad hlen hall
  have eM : β - 1 + r + 1 = β + r := by omega
  constructor
  · have h1 := ev2 hE hSh S ok hC k pad i n Δ ψ nb r i₀ β hok hK hW hocc hmΔ hnb hLD hr hcap hFit Ls Ls.length hlt'.le hLs
      (tent_mono (lam_subset ψ.length Ls cur) hT) [1, -2] [nb + 1, 0] [nb + 1, β - 1 + r]
      (getD2 hnbc le_rfl)
    have h2 := hA n r nb (β - 1 + r) Ls.length ψ _ hψ hWf hlt'.le
    have e1 : ((Ls ++ [cur]) ++ List.replicate (r - (Ls ++ [cur]).length) []).take Ls.length = Ls := by
      rw [List.append_assoc, List.take_left']
      rfl
    unfold sumA at h2
    rw [e1, Lof_pad, eM] at h2
    change evW S k pad i n Δ (mkQ ψ nb r i₀ β) [1, -2] [nb + 1, 0] [nb + 1, β - 1 + r] [ψ, incL n ψ (Ls.take Ls.length) Ls.length] / 2 ^ r ≡ _ [ZMOD 2 ^ β]
    rw [List.take_length, h1]
    exact div_congr h2
  · intro i' hi'
    have hi'' : i' ≤ i₀ := hi'
    have h1 := ev3 hE hSh S ok hC k pad i n Δ ψ nb r i₀ β hok hK hW hocc hmΔ hnb hLD hr hcap hFit (Ls ++ [cur]) Ls.length e hlt'.le hall hT
      [1, -2, 1] [nb + 1, 0, i'] [nb + 1, β - 1 + r, i'] (getD3 hnbc le_rfl (hi''.trans hi₀))
    have h2 := hB n r nb (β - 1 + r) i' Ls.length e ψ _ hψ hWf hlt'
    unfold sumB at h2
    rw [incL_pad, Lof_pad, eM] at h2
    change evW S k pad i n Δ (mkQ ψ nb r i₀ β) [1, -2, 1] [nb + 1, 0, i'] [nb + 1, β - 1 + r, i'] [ψ, incL n ψ (Ls ++ [cur]) Ls.length, ψ.drop e] / 2 ^ r ≡ _ [ZMOD 2 ^ β]
    rw [h1]
    exact div_congr h2
end ClauseBound.ParityChecks.Count
