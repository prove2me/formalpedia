-- Prove2me | solution 1 for ClauseBound.Inst.Half.HalfTabKF.rep_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:41:22.507925+00:00
-- url     : https://prove2.me/submissions/e2f22ff4-8428-419f-bba5-60a388423dac

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTabSpec
import Definitions.Def_ClauseBound_Boson_KF
import Definitions.Def_ClauseBound_Boson_Half
import Definitions.Def_ClauseBound_Inst_HalfTabKF
import Theorems.Thm_ClauseBound_Inst_Half_HalfTabKF_getD_map_range
import Theorems.Thm_ClauseBound_Inst_Half_len_tab_le
import Theorems.Thm_ClauseBound_Inst_Half_rep_tab
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_PaddedDescent_F_Lists_len_list_le
import Theorems.Thm_PaddedDescent_F_cap_eq
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson
open ClauseBound.Inst.Half.HalfTabKF
namespace ClauseBound.Inst.Half.HalfTabKF
theorem _root_.solution {pad : U} {W h B : ℕ} {flat : List (List ℕ)} (hf : FlatOK W flat) {G : ℕ → List ℕ → List ℕ → ℤ} {F : ℕ → ℤ → Ker}
    (hG : ∀ w ≤ h, ∀ π ∈ flat, ∀ σ ∈ flat, G w π σ = F w ((π.sum : ℤ) - σ.sum) π σ)
    (hB : ∀ w r (π σ : Multiset ℕ), π.sum ≤ W → σ.sum ≤ W → |F w r π σ| ≤ 2 ^ B)
    (hp : (h + 1) * (flat.length ^ 2 * (3 * B + 10) + 4) + 2 ≤ pad.length) :
    ∀ w ≤ h, Rep flat ((cap pad [] ((List.range (h + 1)).map fun w => tab flat (G w))).getD w []) (F w) := by
  have hlen : len ((List.range (h + 1)).map fun w => tab flat (G w)) ≤ pad.length := by
    refine le_trans ?_ hp
    have h1 := Lists.len_list_le ((List.range (h + 1)).map fun w => tab flat (G w)) (flat.length ^ 2 * (3 * B + 10) + 4) fun T hT => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hT
      have hw' : w ≤ h := Nat.lt_succ_iff.1 (List.mem_range.1 hw)
      have := len_tab_le (flat := flat) (f := G w) (B := B) fun π hπ σ hσ => by
        rw [hG w hw' π hπ σ hσ]
        exact hB w _ _ _ (by rw [Multiset.sum_coe]; exact hf.sum_le π hπ) (by rw [Multiset.sum_coe]; exact hf.sum_le σ hσ)
      omega
    rwa [List.length_map, List.length_range] at h1
  intro w hw
  rw [cap_eq hlen, getD_map_range hw]
  exact rep_tab (hG w hw)
end ClauseBound.Inst.Half.HalfTabKF
