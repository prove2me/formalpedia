-- Prove2me | solution 1 for CircuitLowerBound.stCertTabF
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T22:33:20.993258+00:00
-- url     : https://prove2.me/submissions/8cbb4498-a28a-4fb1-992a-c28bc7044126
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

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

open CircuitLowerBound
open ENP Groundwork TabF

theorem solution : StCertTabF :=
  ⟨G, G_polyT, fun _ _ _ _ hF hp => G_eq hF hp⟩
