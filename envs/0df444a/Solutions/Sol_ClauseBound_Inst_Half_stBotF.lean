-- Prove2me | solution 1 for ClauseBound.Inst.Half.stBotF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:29:14.455246+00:00
-- url     : https://prove2.me/submissions/07a9573e-032f-482b-8979-ee839cb67770

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfVal
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Definitions.Def_ClauseBound_Inst_HalfTabKF
import Definitions.Def_ClauseBound_Inst_HalfTabBot
import Definitions.Def_ClauseBound_Inst_HalfPad
import Theorems.Thm_ClauseBound_Inst_Half_Pad_parts_of_mem
import Theorems.Thm_ClauseBound_Inst_Half_Pad_padOp_le_padLen
import Theorems.Thm_ClauseBound_Inst_Half_botF_eq
import Theorems.Thm_ClauseBound_Inst_Half_flatOK_allTab


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions
open Pad
namespace ClauseBound.Inst.Half
theorem _root_.solution : StBotF := fun _pad h hh hp _μ hμ hs r _π hπ _σ hσ =>
  botF_eq (by omega) (flatOK_allTab _) (parts_of_mem hμ hs).2 (le_trans (padOp_le_padLen hμ hs) hp) h r hπ hσ
end ClauseBound.Inst.Half
