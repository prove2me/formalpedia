-- Prove2me | solution 1 for CountKSatRate.Pad.length_pad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:52:12.598462+00:00
-- url     : https://prove2.me/submissions/c97a3630-e5ea-4d05-9c1b-71c03941e7c6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_CountKSat_Host
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_CountKSatRate_Pad
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
open CountKSatRate CountKSatRate.Pad
open Groundwork PaddedDescent Turing
variable {e : List Bool → ℕ} {B : List Bool × List Unit → List Bool}
namespace CountKSatRate.Pad
theorem _root_.solution (k : ℕ) : (pad k).length = 2 ^ k := List.length_replicate
end CountKSatRate.Pad
