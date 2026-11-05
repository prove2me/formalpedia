-- Prove2me | solution 1 for ClauseBound.ParityChecks.Bridge.truncW2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:13:25.154738+00:00
-- url     : https://prove2.me/submissions/a92d36aa-77d2-4577-95c2-5e7cf94d9f5c

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
theorem _root_.solution (N : ℕ) (w₀ w₁ : ℤ) (l₀ l₁ h₀ h₁ : ℕ) (L₀ L₁ : Fml) :
    truncW N [w₀, w₁] [l₀, l₁] [h₀, h₁] [L₀, L₁] = ∑ σ : Fin N → Bool,
      (∑ q ∈ Icc l₀ h₀, w₀ ^ q * ((nvio (PaddedDescent.F.Mark.ext σ) L₀).choose q : ℤ)) *
        ((∑ q ∈ Icc l₁ h₁, w₁ ^ q * ((nvio (PaddedDescent.F.Mark.ext σ) L₁).choose q : ℤ)) * 1) := rfl
end ClauseBound.ParityChecks.Bridge
