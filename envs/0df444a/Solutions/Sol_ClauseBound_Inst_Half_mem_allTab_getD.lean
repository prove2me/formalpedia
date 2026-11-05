-- Prove2me | solution 1 for ClauseBound.Inst.Half.mem_allTab_getD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:46:00.715472+00:00
-- url     : https://prove2.me/submissions/01014b26-afb1-4040-b5a0-704e132026f1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_ListP
import Definitions.Def_ClauseBound_Part_Bits
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_PaddedDescent_F_Fuel
import Definitions.Def_ClauseBound_Inst_HalfPart
import Theorems.Thm_ClauseBound_Inst_Half_allTab_getD
import Theorems.Thm_ClauseBound_Part_mem_partsOf
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions Finset
namespace ClauseBound.Inst.Half
theorem _root_.solution {W E : ℕ} (h : E ≤ W) {L : List ℕ} :
    L ∈ (allTab W).getD E [] ↔ L.sum = E ∧ (∀ n ∈ L, 1 ≤ n) ∧ L.Pairwise (· ≥ ·) := by
  rw [allTab_getD h, mem_partsOf]
end ClauseBound.Inst.Half
