-- Prove2me | solution 1 for ClauseBound.Inst.Rec.sgnZ_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:13:31.930034+00:00
-- url     : https://prove2.me/submissions/4b2da38d-23ed-4367-93ea-d1ad11f22a47

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Data
import Definitions.Def_ClauseBound_Rec_Defs
import Definitions.Def_ClauseBound_Rec_CountRow
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Inst_RecArith

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Rec
open Finset Polynomial Groundwork PaddedDescent.F ClauseBound.Rec
namespace ClauseBound.Inst.Rec
theorem _root_.solution (a : ℤ) : sgnZ a = if Even a then 1 else -1 := by
  unfold sgnZ
  refine if_congr ?_ rfl rfl
  rw [← Int.natAbs_even, Nat.even_iff]
end ClauseBound.Inst.Rec
