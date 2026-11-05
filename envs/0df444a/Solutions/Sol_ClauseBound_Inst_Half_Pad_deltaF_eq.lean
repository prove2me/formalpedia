-- Prove2me | solution 1 for ClauseBound.Inst.Half.Pad.deltaF_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:32:49.872896+00:00
-- url     : https://prove2.me/submissions/1653d515-5bc4-411e-9b8d-8cb34242ceba

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfVal
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Definitions.Def_ClauseBound_Inst_HalfTabKF
import Definitions.Def_ClauseBound_Inst_HalfTabBot
import Definitions.Def_ClauseBound_Inst_HalfPad
import Theorems.Thm_ClauseBound_Inst_Half_pTab_eq
import Theorems.Thm_ClauseBound_Inst_Half_sum_map_range
import Theorems.Thm_Groundwork_Stepped_sum_map_range


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions
open ClauseBound.Inst.Half.Pad
namespace ClauseBound.Inst.Half.Pad
theorem _root_.solution (h : ℕ) : deltaF h = ∑ E ∈ Finset.range (4 * h + 1), p E := by
  rw [deltaF, pTab_eq, sum_map_range]
end ClauseBound.Inst.Half.Pad
