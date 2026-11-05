-- Prove2me | solution 1 for ClauseBound.ParityChecks.Bridge.sum_Icc_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:14:13.760529+00:00
-- url     : https://prove2.me/submissions/41219fb6-c29c-417e-8af2-989c02bb1cad

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_BridgeInc
import Definitions.Def_ClauseBound_ParityChecks_StepOne
import Definitions.Def_ClauseBound_ParityChecks_Bridge

set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Bridge
open Groundwork.Prog (Fml)
open PaddedDescent.F.Mark (nvio vio nSat)
open ClauseBound.TopN.EvalW (truncW)
open ClauseBound.ParityChecks ClauseBound.ParityChecks.BridgeInc
namespace ClauseBound.ParityChecks.Bridge
theorem _root_.solution (a v : ℕ) : ∑ q ∈ Icc a a, (1 : ℤ) ^ q * (v.choose q : ℤ) = (v.choose a : ℤ) := by
  rw [Icc_self, sum_singleton, one_pow, one_mul]
end ClauseBound.ParityChecks.Bridge
