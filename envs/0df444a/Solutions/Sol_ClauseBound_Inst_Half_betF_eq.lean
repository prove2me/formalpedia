-- Prove2me | solution 1 for ClauseBound.Inst.Half.betF_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:23:01.889217+00:00
-- url     : https://prove2.me/submissions/ec273788-ed84-41a3-b155-2cef3c857492

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTab
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_ClauseBound_Inst_HalfTabSpec
import Theorems.Thm_ClauseBound_Inst_Rec_chooseZ_eq


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson
namespace ClauseBound.Inst.Half
theorem _root_.solution {W n : ℕ} (hn : n ≤ W) (r : ℤ) : betF W n r = bet n r := by
  rw [betF, bet, min_eq_left hn, chooseZ_eq]
end ClauseBound.Inst.Half
