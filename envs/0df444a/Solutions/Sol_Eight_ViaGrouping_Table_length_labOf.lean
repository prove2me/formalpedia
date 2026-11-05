-- Prove2me | solution 1 for Eight.ViaGrouping.Table.length_labOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:20:04.878219+00:00
-- url     : https://prove2.me/submissions/aaf0f95c-9499-48e0-a756-612be23aabea

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Table
import Theorems.Thm_Eight_ViaGrouping_Table_cap_symm
import Theorems.Thm_Eight_ViaGrouping_Table_mem_members
import Theorems.Thm_Eight_ViaGrouping_Table_length_lAt
import Theorems.Thm_Eight_ViaGrouping_Table_mem_prs
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_NetE_cap_symm
import Theorems.Thm_Groundwork_Prog_NetE_length_lAt
import Theorems.Thm_Groundwork_Prog_NetE_mem_members
import Theorems.Thm_Groundwork_Prog_NetE_mem_prs
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Table
variable {C : Type} [HasSize C] {K g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
variable {x β : ℕ} {G : Fin K} {θ : Fin K → List Bool}
namespace Eight.ViaGrouping.Table
theorem _root_.solution (h : IsNetworkP Np c N P B τ S) (hβ : ∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g Np.toPaperNetwork c x G G' ≤ β)
    (hθ : ∀ G', G' ≠ G → (θ G').length = β) {a b : ℕ} (ha : a ∈ members K g x G) (hb : b < g) (hc : col K x b ≠ G) :
    (labOf K g Np.toPaperNetwork ((c, x), (G.val, List.ofFn θ)) a b).length = Np.cap c a b := by
  have hK : 0 < K := G.pos
  have hG' : col K x b < K := Nat.mod_lt _ hK
  have hbm : b ∈ members K g x (col K x b) := mem_members.2 ⟨hb, rfl⟩
  have hget : (List.ofFn θ).getD (col K x b) [] = θ ⟨col K x b, hG'⟩ := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hG']
    rfl
  have hlen : ((List.ofFn θ).getD (col K x b) []).length = β := by
    rw [hget]
    exact hθ _ fun h => hc (congrArg Fin.val h)
  unfold labOf
  by_cases hlt : G.val < col K x b
  · rw [if_pos hlt]
    exact length_lAt _ (mem_prs ha hbm) (by rw [hlen]; exact hβ _ G.2 _ hG' (Ne.symm hc))
  · rw [if_neg hlt, length_lAt _ (mem_prs hbm ha) (by rw [hlen]; exact hβ _ hG' _ G.2 hc)]
    exact cap_symm h ⟨b, hb⟩ ⟨a, (mem_members.1 ha).1⟩
end Eight.ViaGrouping.Table
