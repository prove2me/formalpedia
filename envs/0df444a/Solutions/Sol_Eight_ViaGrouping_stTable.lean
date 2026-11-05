-- Prove2me | solution 1 for Eight.ViaGrouping.stTable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:57:45.308853+00:00
-- url     : https://prove2.me/submissions/0782f667-feb0-4501-b51e-47f3a65af743

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Table
import Theorems.Thm_Eight_ViaGrouping_Table_isPaperNetwork
import Theorems.Thm_Eight_ViaGrouping_Table_abs_entry_le
import Theorems.Thm_Eight_ViaGrouping_Table_tableM_runs_coarse
import Theorems.Thm_Eight_ViaGrouping_Table_lbLen_eq_Y
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_NetE_length_members
import Theorems.Thm_Groundwork_Prog_NetE_toInst_eq_mergedVal
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Table
namespace Eight.ViaGrouping
theorem _root_.solution : StTable := by
  intro K g
  obtain ⟨c₁, h1, hc₁⟩ := tableM_runs_coarse K g
  refine ⟨c₁, h1, fun hK0 C _ Np c N P B τ S h x hx L hL hG1 hY γ Θ hΘ hγ => ?_⟩
  have hmem : ∀ G < K, (members K g x G).length ≤ 2 * g / K := fun G hG => by
    rw [length_members hK0 x ⟨G, hG⟩, Nat.le_div_iff_mul_le hK0, Nat.mul_comm]
    exact hG1 ⟨G, hG⟩
  have hlb : ∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g Np.toPaperNetwork c x G G' ≤ L := fun G hG G' hG' hne => by
    have hne' : (⟨G, hG⟩ : Fin K) ≠ ⟨G', hG'⟩ := fun e => hne (congrArg Fin.val e)
    rw [lbLen_eq_Y h hK0 x hne']
    exact hY _ _ hne'
  rw [Paper.groupedTables, toInst_eq_mergedVal Np.toPaperNetwork hK0 (isPaperNetwork h).presented x L γ Θ hΘ]
  exact ⟨hc₁ C Np c N P B τ S h x hx L hL _ (Nat.div_le_self _ _) hmem hlb γ Θ hΘ hγ, abs_entry_le h _ hmem hlb hΘ⟩
end Eight.ViaGrouping
