-- Prove2me | solution 1 for Eight.ViaGrouping.stBridge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:09:56.077824+00:00
-- url     : https://prove2.me/submissions/d6345ad2-bef8-4a04-a258-35010087cc86

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Bridge
import Theorems.Thm_Eight_ViaGrouping_value_ofNetwork
import Theorems.Thm_Eight_ViaGrouping_U_ofNetwork
import Theorems.Thm_Eight_ViaGrouping_isNetworkP_ofNetwork

set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Finset Stepped Eight.SecNetworks
variable {g : ℕ}
namespace Eight.ViaGrouping
theorem _root_.solution : StBridge := fun _ _ _ _ _ _ _ N _ _ _ _ hP hτ h hPf hQ => ⟨isNetworkP_ofNetwork hP hτ h hPf hQ, value_ofNetwork N _, U_ofNetwork N _⟩
end Eight.ViaGrouping
