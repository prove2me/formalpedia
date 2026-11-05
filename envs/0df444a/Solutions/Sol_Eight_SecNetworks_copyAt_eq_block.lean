-- Prove2me | solution 1 for Eight.SecNetworks.copyAt_eq_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:07:33.664324+00:00
-- url     : https://prove2.me/submissions/4e44919b-5147-4602-8f8b-dcf21de8ae62

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_Defs
import Definitions.Def_StepMachines_Prog_NetVal
import Mathlib.Tactic
import Definitions.Def_Eight_SecNetworks_Clique

set_option autoImplicit false
section
section
open Eight Eight.SecNetworks
open Groundwork Groundwork.Prog Finset
namespace Eight.SecNetworks
theorem _root_.solution (lam w w' : ℕ) (z : List Bool) : copyAt lam w w' z = block lam (place w w') z := rfl
end Eight.SecNetworks
