-- Prove2me | solution 1 for Eight.ViaGrouping.tableM_display
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:06:13.681203+00:00
-- url     : https://prove2.me/submissions/027d34c3-b8de-426e-abe7-962d1ec69701

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Table
import Definitions.Def_Eight_SecNetworks_Tables
import Definitions.Def_Eight_SecNetworks_Clique
import Definitions.Def_Eight_ViaGrouping_Display
import Theorems.Thm_Eight_ViaGrouping_groupedTables_eq_display
import Theorems.Thm_Eight_ViaGrouping_stTable
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
variable {C : Type} [HasSize C] {g K : ℕ}
variable {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
namespace Eight.ViaGrouping
theorem _root_.solution (K g : ℕ) : ∃ c₁ : ℕ, 1 ≤ c₁ ∧ ∀ (hK0 : 0 < K) (C : Type) [HasSize C] (Np : Procs C) (c : C) (N : Net g) (P B τ S : ℕ), IsNetworkP Np c N P B τ S →
    ∀ x < K ^ g, ∀ L ≤ 2 * (g * P), (∀ γ : Fin K, K * #{a : Fin g | Paper.grouping hK0 x a = γ} ≤ 2 * g) → (∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L) →
    ∀ (γ : Fin K) (Θ : Fin K → List Bool), (∀ γ', γ' ≠ γ → (Θ γ').length = L) → Θ γ = [] →
      (tableM K g Np).Runs ((c, x), γ.1, List.ofFn Θ) (c₁ * 2 ^ (P * (2 * g / K)) * τ) (S + c₁ * (size c + P + B) ^ c₁) (display Np c N hK0 x γ Θ) ∧
        |display Np c N hK0 x γ Θ| ≤ 2 ^ (P * (2 * g / K) + g ^ 2 * B) := by
  obtain ⟨c₁, h1, hc₁⟩ := stTable K g
  refine ⟨c₁, h1, fun hK0 C _ Np c N P B τ S h x hx L hL hG1 hY γ Θ hΘ hγ => ?_⟩
  rw [← groupedTables_eq_display h hK0 x L hY γ Θ hΘ]
  exact hc₁ hK0 C Np c N P B τ S h x hx L hL hG1 hY γ Θ hΘ hγ
end Eight.ViaGrouping
