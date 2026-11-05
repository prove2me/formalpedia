-- Prove2me | solution 1 for ClauseBound.ParityChecks.Bridge.Vof_eq_empty_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:21:30.386439+00:00
-- url     : https://prove2.me/submissions/4c1d02e9-e900-4970-acf7-23b0158568b6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_BridgeInc
import Definitions.Def_ClauseBound_ParityChecks_StepOne
import Definitions.Def_ClauseBound_ParityChecks_Bridge
import Theorems.Thm_ClauseBound_ParityChecks_Bridge_not_vio_iff
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



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
theorem _root_.solution {n : ℕ} (ψ : Fml) (ξ : Fin n → Bool) :
    Vof ψ ξ = ∅ ↔ ∀ C ∈ ψ, ∃ l ∈ C, PaddedDescent.F.Mark.ext ξ l.1 = l.2 := by
  rw [Vof, filter_eq_empty_iff]
  constructor
  · intro H C hC
    obtain ⟨e, he, rfl⟩ := List.mem_iff_getElem.1 hC
    have h1 := H (mem_univ (⟨e, he⟩ : Fin ψ.length))
    rw [List.getD_eq_getElem _ _ he] at h1
    exact (not_vio_iff _ _).1 h1
  · intro H e _
    have h1 := H _ (List.getElem_mem e.2)
    rw [List.getD_eq_getElem _ _ e.2]
    exact (not_vio_iff _ _).2 h1
end ClauseBound.ParityChecks.Bridge
