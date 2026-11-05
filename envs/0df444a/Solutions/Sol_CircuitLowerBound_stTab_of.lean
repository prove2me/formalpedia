-- Prove2me | solution 1 for CircuitLowerBound.stTab_of
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:31:38.361658+00:00
-- url     : https://prove2.me/submissions/1f88b6c5-b6d4-4af3-b4b1-a1197f25716a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Spec
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Glue
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Turing Tab

theorem solution (h1 : StPack) (h2 : StSpec) (h3 : StSpecTab) : StTab := fun N hfin => by
  have : ∀ k, Finite (N.tm.Γ k) := hfin
  have : Finite (Case N) := inferInstance
  obtain ⟨e, hg, hl, he⟩ := h3 N hfin
  refine ⟨e, fun L P hF => ?_⟩
  rw [h1 e L P hg hF, he, bq, hl]
  exact h2 N (bt e L) P (by have := hF.1; unfold bt; omega) hF.2
