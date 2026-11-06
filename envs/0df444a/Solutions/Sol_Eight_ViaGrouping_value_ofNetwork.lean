-- Prove2me | solution 1 for Eight.ViaGrouping.value_ofNetwork
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:38:40.957698+00:00
-- url     : https://prove2.me/submissions/d0c5fba2-5207-41f4-b43a-e09d2c9f41ad

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Bridge

set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Finset Stepped Eight.SecNetworks
variable {g : ℕ}
namespace Eight.ViaGrouping
theorem _root_.solution (N : Paper.Network (Fin g) (List Bool) (List Bool)) (n : Fin g → ℕ) : (ofNetwork N n).value = N.value := rfl
end Eight.ViaGrouping
