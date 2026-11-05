-- Prove2me | solution 1 for ClauseBound.Inst.Half.roundT_tabK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:38:16.881747+00:00
-- url     : https://prove2.me/submissions/9c047764-66a4-49a9-a1db-aaa742a670b8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_ListP
import Definitions.Def_ClauseBound_Part_Bits
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_PaddedDescent_F_Fuel
import Definitions.Def_ClauseBound_Inst_HalfPart
import Theorems.Thm_ClauseBound_Inst_Half_foldl_stepE

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions Finset
namespace ClauseBound.Inst.Half
theorem _root_.solution (W k : ℕ) : roundT W (k + 1) (tabK W k) = tabK W (k + 1) := foldl_stepE W k (W + 1) le_rfl
end ClauseBound.Inst.Half
