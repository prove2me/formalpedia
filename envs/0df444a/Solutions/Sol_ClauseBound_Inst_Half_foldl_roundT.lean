-- Prove2me | solution 1 for ClauseBound.Inst.Half.foldl_roundT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:40:39.03346+00:00
-- url     : https://prove2.me/submissions/aef4559a-4428-4ead-b59b-94dd90b5bfc9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_ListP
import Definitions.Def_ClauseBound_Part_Bits
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_PaddedDescent_F_Fuel
import Definitions.Def_ClauseBound_Inst_HalfPart
import Theorems.Thm_ClauseBound_Inst_Half_initT_eq
import Theorems.Thm_ClauseBound_Inst_Half_roundT_tabK

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions Finset
namespace ClauseBound.Inst.Half
theorem _root_.solution (W j : ℕ) : (List.range j).foldl (fun old k => roundT W (k + 1) old) (initT W) = tabK W j := by
  induction j with
  | zero => exact initT_eq W
  | succ j ih =>
    rw [List.range_succ, List.foldl_append, ih]
    exact roundT_tabK W j
end ClauseBound.Inst.Half
