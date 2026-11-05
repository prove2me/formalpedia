-- Prove2me | solution 1 for ClauseBound.Inst.Half.Labs.mem_flatten_of_mem_getD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:19:13.222318+00:00
-- url     : https://prove2.me/submissions/6bc18524-b587-41ea-89ed-a790cd7df213

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_ClauseBound_Inst_HalfLabs
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Part Partitions
open Labs
open ClauseBound.Inst.Half.Labs
namespace ClauseBound.Inst.Half.Labs
theorem _root_.solution {γ : Type} {T : List (List γ)} {i : ℕ} {L : γ} (h : L ∈ T.getD i []) : L ∈ T.flatten := by
  by_cases hi : i < T.length
  · rw [List.getD_eq_getElem _ _ hi] at h
    exact List.mem_flatten.2 ⟨_, List.getElem_mem hi, h⟩
  · rw [List.getD_eq_default _ _ (not_lt.1 hi)] at h
    cases h
end ClauseBound.Inst.Half.Labs
