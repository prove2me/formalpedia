-- Prove2me | solution 1 for ClauseBound.Inst.Half.RcolF_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:50:44.101385+00:00
-- url     : https://prove2.me/submissions/c68aeabe-1efa-4808-932e-84dc8b0e0589

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_ListP
import Definitions.Def_ClauseBound_Part_Bits
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_PaddedDescent_F_Fuel
import Definitions.Def_ClauseBound_Inst_HalfPart
import Theorems.Thm_ClauseBound_Inst_Half_sum_map_range
import Theorems.Thm_ClauseBound_Inst_Half_pzF_pTab

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions Finset
namespace ClauseBound.Inst.Half
theorem _root_.solution {h : ℕ} {s : ℤ} (hs : -(2 * h : ℤ) ≤ s) : RcolF h s = Rcol h s := by
  unfold RcolF Rcol
  rw [sum_map_range]
  refine Finset.sum_congr rfl fun i _ => pzF_pTab ?_
  push_cast
  omega
end ClauseBound.Inst.Half
