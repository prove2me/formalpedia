-- Prove2me | solution 1 for ClauseBound.Inst.Half.Val.deltaF_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:51:35.313354+00:00
-- url     : https://prove2.me/submissions/18dfde0d-2a57-42fb-9f0c-d9d751218dc5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Inst_HalfVal
import Theorems.Thm_ClauseBound_Inst_Half_pTab_eq
import Theorems.Thm_ClauseBound_Inst_Half_sum_map_range
import Theorems.Thm_Groundwork_Stepped_sum_map_range


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec Finset
open ClauseBound.Inst.Half.Val
namespace ClauseBound.Inst.Half.Val
theorem _root_.solution (h : ℕ) : deltaF h = ∑ E ∈ range (4 * h + 1), Partitions.p E := by
  rw [deltaF, pTab_eq, sum_map_range]
end ClauseBound.Inst.Half.Val
