-- Prove2me | solution 1 for CircuitLowerBound.stFlip_of
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T22:47:13.694018+00:00
-- url     : https://prove2.me/submissions/88601d2d-650b-447d-b231-50a992a41002
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

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

theorem solution (hV : StVars) : StFlip :=
  ⟨fb, fb_polyT, fun m hm => fb_iff hV m hm⟩
