-- Prove2me | solution 1 for ClauseBound.Inst.Half.Par.abs_sOf_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:53:14.037775+00:00
-- url     : https://prove2.me/submissions/cc2eb224-07b5-4f21-9530-b505d0b2bf2e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Part_Bits
import Definitions.Def_ClauseBound_Part_Bounds
import Definitions.Def_ClauseBound_Inst_HalfPar

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Part ClauseBound.Inst.Rec
open ClauseBound.Inst.Half.Par
namespace ClauseBound.Inst.Half.Par
theorem _root_.solution (h i : ℕ) : |sOf h i| ≤ 2 * (h : ℤ) := by
  unfold sOf
  have h1 : min i (4 * h) ≤ 4 * h := min_le_right _ _
  rw [abs_le]
  constructor <;> omega
end ClauseBound.Inst.Half.Par
