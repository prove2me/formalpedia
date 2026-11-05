-- Prove2me | solution 1 for ClauseBound.Inst.Half.padOp_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:24:00.646424+00:00
-- url     : https://prove2.me/submissions/d428558c-f6c6-40e6-8af7-893ad5e4fe64

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTab
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_ClauseBound_Inst_HalfTabSpec

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson
namespace ClauseBound.Inst.Half
theorem _root_.solution (W Δ : ℕ) {L L' : ℕ} (h : L ≤ L') : padOp W Δ L ≤ padOp W Δ L' := by
  unfold padOp
  gcongr
end ClauseBound.Inst.Half
