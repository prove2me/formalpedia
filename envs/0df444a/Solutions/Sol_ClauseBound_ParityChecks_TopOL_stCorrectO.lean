-- Prove2me | solution 1 for ClauseBound.ParityChecks.TopOL.stCorrectO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:33:43.997379+00:00
-- url     : https://prove2.me/submissions/92b7d86e-d699-48ea-bda2-18c6edf13861

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_PaddedDescent_Choice
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_ClauseBound_ParityChecks_TopOL
import Theorems.Thm_ClauseBound_ParityChecks_TopOL_planAtO_some
import Theorems.Thm_ClauseBound_ParityChecks_TopOL_sq_le_tauOf
import Theorems.Thm_ClauseBound_ParityChecks_TopOL_two_le_nbOf
import Theorems.Thm_ClauseBound_ParityChecks_TopOL_lt_two_mul_nbOf
import Theorems.Thm_ClauseBound_ParityChecks_TopOL_i0_le_capM
import Theorems.Thm_ClauseBound_ParityChecks_exists_n0
import Theorems.Thm_CountKSatRate_Leaf_spec
import Theorems.Thm_CountKSat_CountTop_outW_eq
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
import Theorems.Thm_PaddedDescent_le_of_s0K_le
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
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.TopOL
open Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks
open WidthK (theta bsum leafC)
open PaddedDescent.F.Mark (WfL occ nSat)
namespace ClauseBound.ParityChecks.TopOL
theorem _root_.solution (hC : StCountOL) (hB : StBudgetO) (hPar : StParN) (hWC : StWalkCount) (hBr : StBruteC) (hD : StDecU) : StCorrectO := by
  intro c
  obtain ⟨n₁, hn₁⟩ := exists_n0 c
  refine ⟨max (2 ^ 20) n₁, ?_⟩
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ = max (2 ^ 20) n₁ := ⟨_, rfl⟩
  rw [← hn₀]
  intro Idx _ S e C₀ Q hS slU k n φ hk h3 pad hpad
  have hdec : decU k (SatK.enc k φ) = (List.replicate n (), Decode.toN φ) := hD k n φ hk h3.1
  have hn : nK k (SatK.enc k φ) = n := by rw [nK, hdec, List.length_replicate]
  obtain ⟨i, hi⟩ : ∃ i, i = idxN k Q.pick (SatK.enc k φ) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = precN k Q.pick slU (SatK.enc k φ) := ⟨_, rfl⟩
  have hplan : planO S c n₀ k Q.pick slU (SatK.enc k φ) = planAtO S c n₀ k n i s := by rw [planO, hn, hi, hs]
  have hnum : (bif (planO S c n₀ k Q.pick slU (SatK.enc k φ)).isNone then bruteN k (SatK.enc k φ, pad)
      else numOL S k (idxN k Q.pick (SatK.enc k φ)) (precN k Q.pick slU (SatK.enc k φ)) (SatK.enc k φ, pad)) = SatK.numSat φ := by
    rw [eO, hplan, hn] at hpad
    rw [hplan, ← hi, ← hs]
    cases hpl : planAtO S c n₀ k n i s with
    | none =>
      rw [hpl, Option.getD_none] at hpad
      simpa using hBr k n φ hk h3 pad hpad
    | some v =>
      rw [hpl, Option.getD_some] at hpad
      obtain ⟨⟨c1, c2, c3, c4, c5⟩, c6⟩ := planAtO_some hS hpl
      have hblock : blockN k n s = 2 ^ betaN k s := min_eq_left c2
      obtain ⟨Δ, hΔ⟩ : ∃ Δ, Δ = blockN k n s := ⟨_, rfl⟩
      rw [← hblock, ← hΔ] at c4 c5
      rw [c6, needO, pow_add, ← hΔ] at hpad
      have hp1 : 2 ^ needNet S i (UbOL k (S.K i) n Δ) (PbOL (S.K i) n Δ) 0 ≤ pad.length :=
        le_trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)) hpad
      have hp2 : 2 ^ restO k (S.K i) n s ≤ pad.length := le_trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)) hpad
      obtain ⟨b1, b2, b3, b4⟩ := hB k (S.K i) n s pad.length hk c1 hp2
      rw [← hΔ] at b1 b2
      have q1 : leafC (tauOf s) k + 2 ≤ Δ := by rw [hΔ, hblock]; exact (hPar k n s).1
      have hks : k ≤ s := le_of_s0K_le c1
      have hΔ2 : 2 ≤ Δ := by omega
      have hn20 : 2 ^ 20 ≤ n := le_trans (by rw [hn₀]; exact le_max_left _ _) c3
      have hnn₁ : n₁ ≤ n := le_trans (by rw [hn₀]; exact le_max_right _ _) c3
      have hnb : 2 ≤ nbOf n Δ := two_le_nbOf (by omega) c5
      have hoki : ∃ l, i = Q.idx l := ⟨_, hi.trans (Q.pick_idx _)⟩
      have hK2 : 2 ≤ S.K i := by obtain ⟨l, rfl⟩ := hoki; exact Q.K_two l
      simp only [Option.isNone_some, cond_false, numOL, hn]
      refine hWC k (tauOf s) n φ pad _ hk h3 (sq_le_tauOf hks) b3 b4 fun x hxl hx1 ho hs' => ?_
      obtain ⟨m1, m2, m3, m4⟩ := Leaf.spec hk hx1 ho hs'
      have hlen : (leafM x).length ≤ Δ * n := (m1.trans hxl).trans (Nat.mul_le_mul_right _ q1)
      unfold valO
      rw [← hΔ, hC Idx S (fun i => ∃ l, i = Q.idx l) Q.correct k pad i n Δ (leafM x) (2 / 2 ^ (10 * n)) hoki hK2 m2 (fun v => (m3 v).trans q1) hlen hnb
        (lt_two_mul_nbOf (by omega) (by omega))
        (fun hlt => by
          obtain ⟨e1, e2, e3, -⟩ := hn₁ n hnn₁ Δ (leafM x).length hΔ2 c4 hlt hlen
          exact ⟨e1, e2, e3, i0_le_capM hn20 _ _⟩)
        ⟨hp1, b1, b2⟩, m4]
  unfold AO
  simp only [hnum, hdec]
  exact CountTop.outW_eq _ _ _
end ClauseBound.ParityChecks.TopOL
