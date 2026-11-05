-- Prove2me | solution 1 for CountKSatRate.Pad.len_padded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:42:23.840071+00:00
-- url     : https://prove2.me/submissions/bee71f0a-4cb1-4ae4-bba9-92dd4d9d0986

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_CountKSat_Host
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_CountKSatRate_Pad
import Theorems.Thm_CountKSatRate_Pad_length_pad
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_len_units
import Theorems.Thm_PaddedDescent_length_pad
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
open CountKSatRate CountKSatRate.Pad
open Groundwork PaddedDescent Turing
variable {e : List Bool → ℕ} {B : List Bool × List Unit → List Bool}
namespace CountKSatRate.Pad
theorem _root_.solution (x : List Bool) (k : ℕ) : len (x, pad k) = 3 * x.length + 4 * 2 ^ k + 6 := by
  rw [len_pair, len_bools, len_units, length_pad]; omega
end CountKSatRate.Pad
