-- Prove2me | solution 1 for ClauseBound.ParityChecks.Count.count_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:47:53.246115+00:00
-- url     : https://prove2.me/submissions/24cb57ac-e7d4-456f-832e-efbc541b0aa9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Run
import Definitions.Def_ClauseBound_ParityChecks_RunF
import Definitions.Def_PaddedDescent_F_Eval
import Definitions.Def_PaddedDescent_F_Eval
import Definitions.Def_ClauseBound_ParityChecks_Count
import Theorems.Thm_ClauseBound_ParityChecks_Count_getD2
import Theorems.Thm_ClauseBound_ParityChecks_Count_toNat_eq
import Theorems.Thm_ClauseBound_ParityChecks_Count_nSat_le
import Theorems.Thm_ClauseBound_ParityChecks_Count_ev2
import Theorems.Thm_ClauseBound_ParityChecks_Count_orcOK
import Theorems.Thm_ClauseBound_ParityChecks_RunF_runF_eq
import Theorems.Thm_ClauseBound_ParityChecks_Run_tent_out
import Theorems.Thm_ClauseBound_ParityChecks_run_ok
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
theorem _root_.solution (hB : StBridgeB) (hA : StBridgeA) (hF : StBridgeF) (H2 : ChoiceByPotential) (ε : ℚ) (hβ : n + 2 ≤ β) (hnbn : nb ≤ n)
    (hcase : (r = 0 ∧ ψ.length ≤ nb) ∨ (Hyp (mkQ ψ nb r i₀ β) (2 ^ n) ε ∧ i₀ ≤ β - 1 + r)) :
    countOL S k pad i n Δ (mkQ ψ nb r i₀ β) ψ = nSat n ψ := by
  have hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n := fun C hC' => (hW ψ (by simp) C hC').2.2
  have hRF := RunF.runF_eq S k pad i n Δ (mkQ ψ nb r i₀ β) ψ hFit.lists hr hmΔ
  obtain ⟨R, hR, hlen, hchk, hgood, htent⟩ : ∃ R : List Chk, runF S k pad i n Δ (mkQ ψ nb r i₀ β) ψ = R ∧ R.length = r ∧ (∀ L ∈ R, ChkOK ψ.length L) ∧
      Good (Vof (n := n) ψ) nb r (lam ψ.length R) ∧ Tent (mkQ ψ nb r i₀ β) (lam ψ.length R) := by
    rcases hcase with ⟨hr0, hm⟩ | ⟨hH, hi₀⟩
    · subst hr0
      refine ⟨[], ?_, rfl, fun L hL => absurd hL List.not_mem_nil, fun ξ hξ => ?_, ?_⟩
      · rw [hRF]
        rfl
      · exfalso
        have h1 : #(Vof (n := n) ψ ξ) ≤ ψ.length := (Finset.card_le_univ _).trans (by simp)
        omega
      · refine ⟨by simp, fun j' hj' => absurd hj' (Nat.not_lt_zero _), fun x => ?_⟩
        have hx : (1 : ℚ) ≤ (ψ.length : ℚ) := by exact_mod_cast (Nat.lt_of_le_of_lt (Nat.zero_le _) x.2 : 0 < ψ.length)
        simp only [Finset.range_zero, Finset.filter_empty, Finset.card_empty, pow_zero, mul_one]
        linarith
    · have hcard : Fintype.card (Fin n → Bool) = 2 ^ n := by simp
      rw [← hcard] at hH
      have ho := orcOK hE hSh S ok hC k pad i n Δ ψ nb r i₀ β hok hK hW hocc hmΔ hnb hLD hr hcap hFit hB hA (by omega) (by omega) hi₀
      obtain ⟨g1, g2, g3, g4, g5, g6⟩ := run_ok (mkQ ψ nb r i₀ β) (Vof (n := n) ψ) _ _ H2 hH ho
      exact ⟨_, hRF, g1, g2, g3, Run.tent_out ⟨g4, g5, g6⟩⟩
  have h1 := ev2 hE hSh S ok hC k pad i n Δ ψ nb r i₀ β hok hK hW hocc hmΔ hnb hLD hr hcap hFit R r le_rfl hchk htent [-1, -2] [0, 0] [nb, β - 1 + r]
    (getD2 (by omega) le_rfl)
  have h2 := hF n r nb (β - 1 + r) ψ R hψ ⟨hlen, hchk⟩ hgood
  have e1 : R.take r = R := by rw [← hlen, List.take_length]
  unfold sumF3 at h2
  rw [e1] at h2
  change ((evW S k pad i n Δ (mkQ ψ nb r i₀ β) [-1, -2] [0, 0] [nb, β - 1 + r]
    [ψ, incL n ψ ((runF S k pad i n Δ (mkQ ψ nb r i₀ β) ψ).take r) r] / 2 ^ r) % 2 ^ (n + 1)).toNat = _
  rw [hR, e1, h1]
  exact toNat_eq h2 hβ (nSat_le n ψ)
end ClauseBound.ParityChecks.Count
