-- Prove2me | solution 1 for ClauseBound.Inst.Half.nopE_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:30:40.792511+00:00
-- url     : https://prove2.me/submissions/b355a183-f6bb-4cf3-b540-9b157a53952a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTab
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_ClauseBound_Inst_HalfTabSpec
import Theorems.Thm_ClauseBound_Inst_Half_betF_eq
import Theorems.Thm_ClauseBound_Inst_Half_sum_toFinset_coe
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson
namespace ClauseBound.Inst.Half
theorem _root_.solution {W n : ℕ} {flat : List (List ℕ)} {T : List ℤ} {F : ℤ → Ker} (hf : FlatOK W flat) (hn : n ≤ W) (hT : Rep flat T F) {π σ : List ℕ}
    (hπ : π ∈ flat) (hσ : σ ∈ flat) : nopE W n flat T π σ = nop n F ((π.sum : ℤ) - σ.sum) π σ := by
  rw [nopE, nop, sum_toFinset_coe, sum_toFinset_coe]
  congr 1
  · refine congrArg List.sum (List.map_congr_left fun l hl => ?_)
    have hl' : l ∈ π := List.mem_dedup.1 hl
    have hs : ((π.erase l).sum : ℤ) - σ.sum = (π.sum : ℤ) - σ.sum - l := by
      have := List.sum_erase hl'
      push_cast [← this]
      ring
    rw [betF_eq hn, hT _ (hf.erase π hπ l hl') σ hσ, hs, cre, if_pos (Multiset.mem_coe.2 hl'), Multiset.coe_erase]
  · refine congrArg List.sum (List.map_congr_left fun k hk => ?_)
    have hk' : k ∈ σ := List.mem_dedup.1 hk
    have hs : (π.sum : ℤ) - (σ.erase k).sum = (π.sum : ℤ) - σ.sum + k := by
      have := List.sum_erase hk'
      push_cast [← this]
      ring
    rw [betF_eq hn, hT π hπ _ (hf.erase σ hσ k hk'), hs, ann, Multiset.coe_count, Multiset.coe_erase]
end ClauseBound.Inst.Half
