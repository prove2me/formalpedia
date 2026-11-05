-- Prove2me | solution 1 for ClauseBound.Inst.Half.stWords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:33:04.022679+00:00
-- url     : https://prove2.me/submissions/64e212f3-6c2c-4534-9c99-de0875275407

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_ClauseBound_Inst_HalfLabs
import Theorems.Thm_ClauseBound_Inst_Half_sum_words_getElem

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Part Partitions
open Labs
namespace ClauseBound.Inst.Half
theorem _root_.solution : StWords := fun _ L c f g hL => sum_words_getElem L c hL f g
end ClauseBound.Inst.Half
