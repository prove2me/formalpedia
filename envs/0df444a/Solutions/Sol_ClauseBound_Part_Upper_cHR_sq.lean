-- Prove2me | solution 1 for ClauseBound.Part.Upper.cHR_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:26:07.113284+00:00
-- url     : https://prove2.me/submissions/a53168c2-e179-4bb4-936a-47c74e5ac56e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_Rec
import Definitions.Def_ClauseBound_Part_Upper

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ClauseBound.Part.Upper
namespace ClauseBound.Part.Upper
theorem _root_.solution : cHR ^ 2 = 2 * Real.pi ^ 2 / 3 := by
  rw [cHR, mul_pow, Real.sq_sqrt (by norm_num)]
  ring
end ClauseBound.Part.Upper
