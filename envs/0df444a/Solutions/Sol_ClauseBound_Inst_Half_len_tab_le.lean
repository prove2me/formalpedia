-- Prove2me | solution 1 for ClauseBound.Inst.Half.len_tab_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:30:32.715966+00:00
-- url     : https://prove2.me/submissions/f89aae6e-de7b-4654-9452-7dace6123cd6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTab
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_ClauseBound_Inst_HalfTabSpec
import Theorems.Thm_ClauseBound_Inst_Half_length_tab
import Theorems.Thm_ClauseBound_Inst_Half_len_int_le
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_PaddedDescent_F_Lists_len_list_le
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson
namespace ClauseBound.Inst.Half
theorem _root_.solution {flat : List (List ℕ)} {f : List ℕ → List ℕ → ℤ} {B : ℕ} (h : ∀ π ∈ flat, ∀ σ ∈ flat, |f π σ| ≤ 2 ^ B) :
    len (tab flat f) ≤ flat.length ^ 2 * (3 * B + 10) + 2 := by
  rw [← length_tab flat f]
  refine Lists.len_list_le _ _ fun z hz => ?_
  obtain ⟨π, hπ, hz⟩ := List.mem_flatMap.1 hz
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hz
  have := len_int_le (h π hπ σ hσ)
  omega
end ClauseBound.Inst.Half
