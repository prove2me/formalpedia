-- Prove2me | solution 1 for ClauseBound.Inst.Half.Pad.parts_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:53:12.920259+00:00
-- url     : https://prove2.me/submissions/bb814f36-f646-419f-bb94-d2a3f4287104

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfVal
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Definitions.Def_ClauseBound_Inst_HalfTabKF
import Definitions.Def_ClauseBound_Inst_HalfTabBot
import Definitions.Def_ClauseBound_Inst_HalfPad
import Theorems.Thm_ClauseBound_Boson_Size_le_sum_of_mem
import Theorems.Thm_ClauseBound_Inst_Half_mem_flatten_allTab
import Theorems.Thm_ClauseBound_Part_ListP_le_sum_of_mem
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions
open ClauseBound.Inst.Half.Pad
namespace ClauseBound.Inst.Half.Pad
theorem _root_.solution {h : ℕ} {μ : List ℕ} (hμ : μ ∈ (allTab (4 * h)).flatten) (hs : μ.sum = h) :
    μ.length ≤ h ∧ ∀ n ∈ μ, n ≤ 4 * h := by
  obtain ⟨_, h2, _⟩ := mem_flatten_allTab.1 hμ
  refine ⟨hs ▸ List.length_le_sum_of_one_le μ h2, fun n hn => ?_⟩
  have := List.le_sum_of_mem hn
  omega
end ClauseBound.Inst.Half.Pad
