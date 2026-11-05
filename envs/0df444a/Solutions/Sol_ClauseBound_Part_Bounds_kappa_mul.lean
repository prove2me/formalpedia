-- Prove2me | solution 1 for ClauseBound.Part.Bounds.kappa_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:33:32.633516+00:00
-- url     : https://prove2.me/submissions/3464c4a9-14c3-45b6-b1a4-b16988136e83

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_Upper
import Definitions.Def_ClauseBound_Part_Lower
import Definitions.Def_ClauseBound_Part_Bounds

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ClauseBound.Part.Bounds
namespace ClauseBound.Part.Bounds
theorem _root_.solution (x : ℝ) : kappa * x = cHR * x / Real.log 2 := by
  rw [kappa]
  ring
end ClauseBound.Part.Bounds
