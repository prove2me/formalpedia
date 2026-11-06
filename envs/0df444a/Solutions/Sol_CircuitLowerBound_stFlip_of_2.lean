-- Prove2me | solution 2 for CircuitLowerBound.stFlip_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:10:25.39621+00:00
-- url     : https://prove2.me/submissions/86f1e4ed-d589-447b-9af3-9ff46deed2c0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Cert_Sched
import Definitions.Def_CircuitLowerBound_Small
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Cert_TabF
import Theorems.Thm_CircuitLowerBound_TabF_fb_polyT
import Theorems.Thm_CircuitLowerBound_TabF_fb_iff

set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork TabF
namespace CircuitLowerBound
theorem _root_.solution (hV : StVars) : StFlip := ⟨fb, fb_polyT, fun m hm => fb_iff hV m hm⟩
end CircuitLowerBound
