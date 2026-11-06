-- Prove2me | solution 2 for CircuitLowerBound.stCertTabF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:03:23.524844+00:00
-- url     : https://prove2.me/submissions/91c9b909-1c1a-4a49-901d-32496ee4ef02

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Cert_Sched
import Definitions.Def_CircuitLowerBound_Small
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Cert_TabF
import Theorems.Thm_CircuitLowerBound_TabF_G_polyT
import Theorems.Thm_CircuitLowerBound_TabF_G_eq

set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork TabF
namespace CircuitLowerBound
theorem _root_.solution : StCertTabF := ⟨G, G_polyT, fun _ _ _ _ hF hp => G_eq hF hp⟩
end CircuitLowerBound
