-- Prove2me | solution 1 for ClauseBound.Inst.Half.Pad.padOp_le_padLen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:00:55.58118+00:00
-- url     : https://prove2.me/submissions/4fed55db-0cd8-4b67-bd2e-eead84a21c65

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfVal
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Definitions.Def_ClauseBound_Inst_HalfTabKF
import Definitions.Def_ClauseBound_Inst_HalfTabBot
import Definitions.Def_ClauseBound_Inst_HalfPad
import Theorems.Thm_ClauseBound_Inst_Half_Pad_padOp_le_padKF
import Theorems.Thm_ClauseBound_Inst_Half_Pad_padKF_le_padLen
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
    padOp (4 * h) (allTab (4 * h)).flatten.length μ.length ≤ padLen h :=
  le_trans (padOp_le_padKF _ _ h μ.sum _) (padKF_le_padLen hμ hs)
end ClauseBound.Inst.Half.Pad
