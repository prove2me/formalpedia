-- Prove2me | solution 1 for CircuitLowerBound.sat_by_circuit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:11:00.778212+00:00
-- url     : https://prove2.me/submissions/e819de84-456b-43a5-9f6c-8b982c75f184

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Interfaces
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Main
import Theorems.Thm_CircuitLowerBound_phi_vars
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_ofWord_toWord
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork Turing
namespace CircuitLowerBound
theorem _root_.solution (hG : StGreedy) (hV : StVars) {m : ℕ} {C : Circuit} (hC : ∀ x : List Bool, x.length = m → (eval C x = true ↔ L0 x))
    (hs : Sat (Phi m)) : ∀ D ∈ Phi m, ∃ l ∈ D, eval C (toWord m l.1) = l.2 := by
  intro D hD
  obtain ⟨l, hl, hval⟩ := hG (Phi m) (2 ^ m) (phi_vars hV m) hs D hD
  refine ⟨l, hl, ?_⟩
  have h1 := hC (toWord m l.1) (length_toWord _ _)
  unfold L0 at h1
  rw [length_toWord, ofWord_toWord (phi_vars hV m D hD l hl), hval] at h1
  cases h2 : l.2 <;> cases h3 : eval C (toWord m l.1) <;> simp_all
end CircuitLowerBound
