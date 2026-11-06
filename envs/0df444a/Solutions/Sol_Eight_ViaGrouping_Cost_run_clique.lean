-- Prove2me | solution 1 for Eight.ViaGrouping.Cost.run_clique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:45:50.349195+00:00
-- url     : https://prove2.me/submissions/557f489b-3900-49b4-ac55-e63fd74d79c9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Search
import Definitions.Def_StepMachines_Math_RebalanceArith
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Main
import Theorems.Thm_Eight_ViaGrouping_Cost_serves_Bp
import Theorems.Thm_Eight_SecNetworks_L_le
import Theorems.Thm_Eight_SecNetworks_U_le
import Theorems.Thm_Eight_ViaGrouping_Y_le_of_good
import Theorems.Thm_Eight_ViaGrouping_lamP_eq
import Theorems.Thm_Groundwork_Colouring_one_le_beta
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Cost
namespace Eight.ViaGrouping.Cost
theorem _root_.solution (hT : StTable) (hV : StValue) {K : ℕ} (g : ℕ) {e : ℝ} {E : Paper.CliqueAlgorithm} (hK0 : 0 < K) (hg : 1 ≤ g) (h : E.Within K e) :
    ∃ A c₁ : ℕ, 1 ≤ c₁ ∧ ∀ (C : Type) [HasSize C] (Np : Procs C) (c : C) (N : Net g) (P B τ S : ℕ), IsNetworkP Np c N P B τ S →
      ∀ x < K ^ g, Good N.c P (Paper.grouping hK0 x) →
      ∃ TE : ℕ, (E.app (lamP K g Np) (tableM K g Np)).Runs (c, x) TE
          (S + c₁ * (size c + P + B) ^ c₁ + A * (size (c, x) + Bp K g P B + Paper.groupedLength K g N.U P) ^ A) N.value ∧
        (TE : ℝ) ≤ A * (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * (Paper.groupedLength K g N.U P : ℝ)) * ((Bp K g P B : ℝ) + (Paper.groupedLength K g N.U P : ℝ)) ^ A
          * ((c₁ * 2 ^ (P * (2 * g / K)) * τ : ℕ) : ℝ) := by
  obtain ⟨A, hA⟩ := h
  obtain ⟨c₁, h1, hc₁⟩ := hT K g
  refine ⟨A, c₁, h1, fun C _ Np c N P B τ S hN x hx hgood => ?_⟩
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = Paper.groupedLength K g N.U P := ⟨_, rfl⟩
  rw [← hL]
  have hlam : lamP K g Np (c, x) = L := (lamP_eq hN x).trans hL.symm
  have hL1 : 1 ≤ L := hL ▸ Colouring.one_le_beta _ _ _ _
  have hLle : L ≤ 2 * (g * P) := hL ▸ L_le hK0 hg hN.is.P_pos (U_le hN.is)
  have hY : ∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L := fun γ γ' hne => hL ▸ Y_le_of_good hK0 hgood hne
  have hserve := serves_Bp g P B (hc₁ hK0 C Np c N P B τ S hN x hx L hLle hgood.G1 hY)
  have ht' : 1 ≤ c₁ * 2 ^ (P * (2 * g / K)) * τ := Nat.mul_pos (Nat.mul_pos h1 (Nat.two_pow_pos _)) hN.τ_pos
  obtain ⟨TE, hrun, hTE⟩ := hA (C × ℕ) (lamP K g Np) (tableM K g Np) (c, x) (Bp K g P B) _ _ _ (hlam ▸ hL1) ht' (hlam ▸ hserve)
  rw [hlam, show Inst.ZW L [] (Paper.groupedTables Np.toPaperNetwork c N.toPaperNetwork hK0 x L) = N.value from hV K g hK0 C Np c N P B τ S hN x L hY] at hrun
  rw [hlam] at hTE
  exact ⟨TE, hrun, hTE⟩
end Eight.ViaGrouping.Cost
