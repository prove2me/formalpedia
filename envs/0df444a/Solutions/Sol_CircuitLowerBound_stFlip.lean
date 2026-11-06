-- Prove2me | solution 1 for CircuitLowerBound.stFlip
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T00:26:45.665435+00:00
-- url     : https://prove2.me/submissions/46c47b39-7488-44b0-be6a-f5bd086a1eab

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Cert_Sched
import Definitions.Def_CircuitLowerBound_Small
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Cert_TabF
import Theorems.Thm_CircuitLowerBound_TabF_fb_polyT
import Theorems.Thm_CircuitLowerBound_TabF_fb_iff
import Theorems.Thm_CircuitLowerBound_stVars
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork TabF

theorem solution : StFlip := by
  exact ⟨fb, fb_polyT, fun m hm => fb_iff stVars m hm⟩
