-- Prove2me | solution 1 for ClauseBound.Part.Bounds.logb_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:33:20.156435+00:00
-- url     : https://prove2.me/submissions/dd320223-b6c8-4384-8f90-2ad0cd0fd7cc

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
theorem _root_.solution (x : ℝ) : Real.logb 2 (Real.exp x) = x / Real.log 2 := by rw [Real.logb, Real.log_exp]
end ClauseBound.Part.Bounds
