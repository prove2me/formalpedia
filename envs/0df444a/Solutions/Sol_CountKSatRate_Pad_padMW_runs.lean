-- Prove2me | solution 1 for CountKSatRate.Pad.padMW_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:59:47.59302+00:00
-- url     : https://prove2.me/submissions/dd0ef8c1-d3a1-4516-85b1-c3ba2c3902e6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_CountKSat_Host
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_CountKSatRate_Pad
import Theorems.Thm_CountKSatRate_Pad_padMW_reaches
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
open CountKSatRate CountKSatRate.Pad
open Groundwork PaddedDescent Turing
variable {e : List Bool → ℕ} {B : List Bool × List Unit → List Bool}
namespace CountKSatRate.Pad
theorem _root_.solution (e : List Bool → ℕ) (B : List Bool × List Unit → List Bool) (x : List Bool) :
    (padMW e B).Runs x (e x + 1) (2 * x.length + 2 * 2 ^ e x + 3 + (2 * (B (x, pad (e x))).length + 2)) (B (x, pad (e x))) :=
  padMW_reaches x (e x) 0 (by omega)
end CountKSatRate.Pad
