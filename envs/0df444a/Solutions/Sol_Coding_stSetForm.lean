-- Prove2me | solution 1 for Coding.stSetForm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:01:39.482177+00:00
-- url     : https://prove2.me/submissions/70bba0e3-084b-4ac1-b0bf-a9511a066c43

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_Sets
import Definitions.Def_Exits_End
import Definitions.Def_Coding_SetForm
import Theorems.Thm_Coding_stSetFormOf
import Theorems.Thm_Coding_stWrites
import Theorems.Thm_Exits_threeSat_by_algorithm


set_option autoImplicit false
section
section
open Coding
namespace Coding
theorem _root_.solution : StSetForm := stSetFormOf stWrites Exits.threeSat_by_algorithm
end Coding
