-- Prove2me | solution 1 for CircuitLowerBound.SmallFacts.sat_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:55:08.91996+00:00
-- url     : https://prove2.me/submissions/3781ecfd-4f62-428d-9e0c-652adc1ddb31

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Interfaces
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Small

set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.SmallFacts
namespace CircuitLowerBound.SmallFacts
theorem _root_.solution {φ ψ : Cnf} {a : ℕ → Bool} : (∀ C ∈ φ ++ ψ, ∃ l ∈ C, a l.1 = l.2) ↔ (∀ C ∈ φ, ∃ l ∈ C, a l.1 = l.2) ∧ ∀ C ∈ ψ, ∃ l ∈ C, a l.1 = l.2 :=
  List.forall_mem_append
end CircuitLowerBound.SmallFacts
