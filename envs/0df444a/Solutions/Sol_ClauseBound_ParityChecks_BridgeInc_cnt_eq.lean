-- Prove2me | solution 1 for ClauseBound.ParityChecks.BridgeInc.cnt_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:30:55.01985+00:00
-- url     : https://prove2.me/submissions/8d4916f9-f363-4889-a4fb-dbd92523f01e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_NetDefs
import Definitions.Def_ClauseBound_ParityChecks_Dummy
import Definitions.Def_ClauseBound_ParityChecks_BridgeInc
import Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_countP_idx
import Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_vio_getD
import Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_wf_getD

set_option autoImplicit false
section
section
open Finset Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.BridgeInc
namespace ClauseBound.ParityChecks.BridgeInc
theorem _root_.solution {n r : ℕ} (σ : Fin (n + r) → Bool) {ψ : Fml} (h : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) {r' : ℕ} {Lam : List (List ℕ)} (hL : WfC ψ r' Lam) (j : ℕ) :
    cnt (ext σ) ψ Lam j = #(Lof ψ Lam j ∩ Vof ψ (xi σ)) := by
  obtain ⟨h1, h2⟩ := wf_getD hL j
  rw [cnt, countP_idx h1 h2, Lof, Vof, ← filter_and]
  exact congrArg card (filter_congr fun e _ => by rw [vio_getD σ h])
end ClauseBound.ParityChecks.BridgeInc
