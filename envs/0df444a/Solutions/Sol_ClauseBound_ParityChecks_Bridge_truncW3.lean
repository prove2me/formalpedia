-- Prove2me | solution 1 for ClauseBound.ParityChecks.Bridge.truncW3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:12:56.717391+00:00
-- url     : https://prove2.me/submissions/845413fb-7436-4ae8-bf28-9c745cf73893

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
theorem _root_.solution (N : ℕ) (w₀ w₁ w₂ : ℤ) (l₀ l₁ l₂ h₀ h₁ h₂ : ℕ) (L₀ L₁ L₂ : Fml) :
    truncW N [w₀, w₁, w₂] [l₀, l₁, l₂] [h₀, h₁, h₂] [L₀, L₁, L₂] = ∑ σ : Fin N → Bool,
      (∑ q ∈ Icc l₀ h₀, w₀ ^ q * ((nvio (PaddedDescent.F.Mark.ext σ) L₀).choose q : ℤ)) *
        ((∑ q ∈ Icc l₁ h₁, w₁ ^ q * ((nvio (PaddedDescent.F.Mark.ext σ) L₁).choose q : ℤ)) *
          ((∑ q ∈ Icc l₂ h₂, w₂ ^ q * ((nvio (PaddedDescent.F.Mark.ext σ) L₂).choose q : ℤ)) * 1)) := rfl
end ClauseBound.ParityChecks.Bridge
