-- Prove2me | solution 1 for CircuitLowerBound.SmallFacts.sat_units
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:55:09.966247+00:00
-- url     : https://prove2.me/submissions/076b2d41-1572-4d5a-8876-62ee4020f751

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Interfaces
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Small
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.SmallFacts
namespace CircuitLowerBound.SmallFacts
theorem _root_.solution {w : List Bool} {a : ℕ → Bool} : (∀ C ∈ units w, ∃ l ∈ C, a l.1 = l.2) ↔ ∀ i < w.length, a i = w.getD i false := by
  simp [units]
end CircuitLowerBound.SmallFacts
