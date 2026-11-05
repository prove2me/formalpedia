-- Prove2me | solution 1 for ClauseBound.ParityChecks.BridgeInc.disjoint_J
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:12:43.82397+00:00
-- url     : https://prove2.me/submissions/444cbb2a-b778-48d9-83ab-f70fccf4cd43

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_NetDefs
import Definitions.Def_ClauseBound_ParityChecks_Dummy
import Definitions.Def_ClauseBound_ParityChecks_BridgeInc

set_option autoImplicit false
section
section
open Finset Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.BridgeInc
namespace ClauseBound.ParityChecks.BridgeInc
theorem _root_.solution (r j : ℕ) : Disjoint (J1 r j) (J2 r j) := by
  rw [disjoint_left]
  intro a h1 h2
  have h1 := (mem_filter.1 h1).2
  have h2 := (mem_filter.1 h2).2
  omega
end ClauseBound.ParityChecks.BridgeInc
