-- Prove2me | solution 1 for FixedWidthSteps.hypothesisHoldsFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:17:25.931224+00:00
-- url     : https://prove2.me/submissions/9425c852-b523-4e64-8c61-997b0a6e33a0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FixedWidthSteps_RouteDefs
import Definitions.Def_FixedWidthSteps_Hypothesis

set_option autoImplicit false
section
section
open FixedWidthSteps
open PairsToBound FixedWidth
namespace FixedWidthSteps
theorem _root_.solution : HypothesisHoldsFrom := by
  intro hL hC c
  obtain ⟨C₀, h⟩ := hL c
  refine ⟨C₀, fun ρ x₀ P A val hP hx hc => ?_⟩
  obtain ⟨Q, hpoly, hK, hpick⟩ := h ρ x₀ P A val hP hx hc
  refine ⟨Q, hpoly, hK, hpick, fun num hnum hb => ⟨hnum, fun l => ?_⟩⟩
  rw [hK l]
  exact (hC ρ x₀ l hP.rho_ge hP.rho_lt hx).2.2.2 _ (hb l).1 (hb l).2
end FixedWidthSteps
