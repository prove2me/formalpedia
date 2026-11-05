-- Prove2me | solution 1 for ClauseBound.Inst.Half.Pad.length_flatten_allTab_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:41:23.625145+00:00
-- url     : https://prove2.me/submissions/a7543855-46ed-44e0-ad2e-f87a1d5fb74a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfVal
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Definitions.Def_ClauseBound_Inst_HalfTabKF
import Definitions.Def_ClauseBound_Inst_HalfTabBot
import Definitions.Def_ClauseBound_Inst_HalfPad
import Theorems.Thm_ClauseBound_Inst_Half_Pad_length_flatten_allTab
import Theorems.Thm_ClauseBound_Inst_Half_Pad_deltaF_eq
import Theorems.Thm_ClauseBound_Inst_Half_Val_deltaF_eq
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions
open ClauseBound.Inst.Half.Pad
namespace ClauseBound.Inst.Half.Pad
theorem _root_.solution (h : ℕ) : (allTab (4 * h)).flatten.length = deltaF h := by
  rw [length_flatten_allTab, deltaF_eq]
end ClauseBound.Inst.Half.Pad
