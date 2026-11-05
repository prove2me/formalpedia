-- Prove2me | solution 1 for ClauseBound.Inst.Half.stLabs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:45:35.892665+00:00
-- url     : https://prove2.me/submissions/ecd1eba7-0cbd-486a-b14b-41f734afe051

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_ClauseBound_Inst_HalfLabs
import Theorems.Thm_ClauseBound_Inst_Half_mem_flatten_of_mem_labs
import Theorems.Thm_ClauseBound_Inst_Half_length_labs
import Theorems.Thm_ClauseBound_Inst_Half_sum_map_labs

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Part Partitions
open Labs
namespace ClauseBound.Inst.Half
theorem _root_.solution : StLabs := fun tr _ _ hs =>
  ⟨length_labs hs tr, sum_map_labs hs tr, fun _ hp => mem_flatten_of_mem_labs hp⟩
end ClauseBound.Inst.Half
