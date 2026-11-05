-- Prove2me | solution 1 for ClauseBound.ParityChecks.BridgeInc.nvio_drop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:30:52.146108+00:00
-- url     : https://prove2.me/submissions/d6924e63-31dc-44ca-b3fc-70c1f767b0ee

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_NetDefs
import Definitions.Def_ClauseBound_ParityChecks_Dummy
import Definitions.Def_ClauseBound_ParityChecks_BridgeInc
import Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_countP_drop
import Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_vio_getD

set_option autoImplicit false
section
section
open Finset Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.BridgeInc
namespace ClauseBound.ParityChecks.BridgeInc
theorem _root_.solution {n r : ℕ} {ψ : Fml} (h : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) (t : ℕ) (σ : Fin (n + r) → Bool) :
    nvio (ext σ) (ψ.drop t) = #(Dof ψ t ∩ Vof ψ (xi σ)) := by
  rw [nvio, countP_drop _ [], Dof, Vof, ← filter_and]
  exact congrArg card (filter_congr fun e _ => by rw [vio_getD σ h])
end ClauseBound.ParityChecks.BridgeInc
