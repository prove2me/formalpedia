-- Prove2me | solution 2 for CircuitLowerBound.stGreedy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:10:21.299807+00:00
-- url     : https://prove2.me/submissions/34b26a13-4c6b-44db-bf83-0099be82e57e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Interfaces
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Small
import Theorems.Thm_CircuitLowerBound_SmallFacts_length_greedy
import Theorems.Thm_CircuitLowerBound_SmallFacts_greedy_prefix
import Theorems.Thm_CircuitLowerBound_SmallFacts_sat_append
import Theorems.Thm_CircuitLowerBound_SmallFacts_sat_units
import Theorems.Thm_CircuitLowerBound_SmallFacts_sat_greedy

set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open SmallFacts
namespace CircuitLowerBound
theorem _root_.solution : StGreedy := by
  intro φ M hM hs C hC
  obtain ⟨a, ha⟩ := sat_greedy hs M
  obtain ⟨h1, h2⟩ := sat_append.1 ha
  rw [sat_units, length_greedy] at h2
  obtain ⟨l, hl, hal⟩ := h1 C hC
  refine ⟨l, hl, ?_⟩
  have hlt := hM C hC l hl
  obtain ⟨r, hr⟩ := greedy_prefix φ (show l.1 + 1 ≤ M from hlt)
  rw [← hal, h2 l.1 hlt, ← hr, List.getD_append _ _ _ _ (by rw [length_greedy]; omega)]
end CircuitLowerBound
