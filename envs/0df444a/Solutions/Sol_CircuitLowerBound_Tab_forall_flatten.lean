-- Prove2me | solution 1 for CircuitLowerBound.Tab.forall_flatten
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:33:54.831792+00:00
-- url     : https://prove2.me/submissions/b79fda6e-864b-46a9-8e66-af8d14b91692

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Frame
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Table
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Tab
open ENP Turing
variable (N : TM2ComputableAux Bool Bool)
variable {N}
namespace CircuitLowerBound.Tab
theorem _root_.solution {β : Type} {p : β → Prop} {Ls : List (List β)} : (∀ c ∈ Ls.flatten, p c) ↔ ∀ l ∈ Ls, ∀ c ∈ l, p c := by
  simp only [List.mem_flatten]
  exact ⟨fun h l hl c hc => h c ⟨l, hl, hc⟩, fun h c ⟨l, hl, hc⟩ => h l hl c hc⟩
end CircuitLowerBound.Tab
