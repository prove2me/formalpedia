-- Prove2me | solution 1 for ClauseBound.ParityChecks.BridgeInc.wf_getD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:12:42.768924+00:00
-- url     : https://prove2.me/submissions/84c18d48-5131-4153-a812-45a758015512

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_NetDefs
import Definitions.Def_ClauseBound_ParityChecks_Dummy
import Definitions.Def_ClauseBound_ParityChecks_BridgeInc
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Finset Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.BridgeInc
namespace ClauseBound.ParityChecks.BridgeInc
theorem _root_.solution {ψ : Fml} {r : ℕ} {Lam : List (List ℕ)} (h : WfC ψ r Lam) (j : ℕ) : (Lam.getD j []).Nodup ∧ ∀ e ∈ Lam.getD j [], e < ψ.length := by
  by_cases hj : j < Lam.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact h.2 _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact ⟨List.nodup_nil, fun e he => absurd he (List.not_mem_nil)⟩
end ClauseBound.ParityChecks.BridgeInc
