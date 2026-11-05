-- Prove2me | solution 1 for ClauseBound.Inst.Half.pzF_pTab
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:46:35.113421+00:00
-- url     : https://prove2.me/submissions/137d6ba3-db51-4e39-9ff7-da5f5c6f958b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_ListP
import Definitions.Def_ClauseBound_Part_Bits
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_PaddedDescent_F_Fuel
import Definitions.Def_ClauseBound_Inst_HalfPart
import Theorems.Thm_ClauseBound_Inst_Half_pTab_getD

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions Finset
namespace ClauseBound.Inst.Half
theorem _root_.solution {W : ℕ} {E : ℤ} (h : E ≤ W) : pzF (pTab W) E = pz E := by
  unfold pzF pz
  split_ifs with h0
  · exact pTab_getD W _ (by omega)
  · rfl
end ClauseBound.Inst.Half
