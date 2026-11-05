-- Prove2me | solution 1 for ClauseBound.ParityChecks.Bridge.stBridgeA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:53:07.558378+00:00
-- url     : https://prove2.me/submissions/d8d3b929-34fc-4f44-a0af-777e3fcfad0b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_BridgeInc
import Definitions.Def_ClauseBound_ParityChecks_StepOne
import Definitions.Def_ClauseBound_ParityChecks_Bridge
import Theorems.Thm_ClauseBound_ParityChecks_Bridge_sum_Icc_self
import Theorems.Thm_ClauseBound_ParityChecks_Bridge_two_layers

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
theorem _root_.solution : StBridgeA := by
  intro n r nb M j ψ Lam hψ hW hj
  exact two_layers hψ hW hj M 1 (nb + 1) (nb + 1) (fun ξ => (omega (Vof (n := n) ψ) nb ξ : ℤ)) fun ξ => sum_Icc_self _ _
end ClauseBound.ParityChecks.Bridge
