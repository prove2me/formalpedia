-- Prove2me | solution 1 for ClauseBound.Part.Lower.cHR_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:33:14.526873+00:00
-- url     : https://prove2.me/submissions/dea37962-bca7-45a8-aee5-98f11346b044

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_Rec
import Definitions.Def_ClauseBound_Part_Lower

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ClauseBound.Part.Lower
namespace ClauseBound.Part.Lower
theorem _root_.solution : Real.pi ^ 2 / 6 = cHR ^ 2 / 4 := by
  unfold cHR
  rw [mul_pow, Real.sq_sqrt (by norm_num)]
  ring
end ClauseBound.Part.Lower
