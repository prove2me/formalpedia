-- Prove2me | solution 1 for BlackScholesModel.cash_or_nothing_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T17:00:23.082624+00:00
-- url     : https://prove2.me/submissions/230b29b1-8fdc-4cb5-8282-66275183c511

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Theorems.Thm_BlackScholesModel_terminalPrice_strike_events
import Theorems.Thm_BlackScholesModel_gaussianReal_halfline_probs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

/-- Price the digital cash-or-nothing claims using Gaussian half-line masses. -/
theorem solution (K r σ T S t : ℝ)
    (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S) (ht : t < T) :
    Real.exp (-r * (T - t)) *
        (gaussianReal 0 1).real {z | K < terminalPrice S r σ (T - t) z}
      = Real.exp (-r * (T - t)) *
        stdNormalCDF (dMinus S K r σ (T - t)) ∧
    Real.exp (-r * (T - t)) *
        (gaussianReal 0 1).real {z | terminalPrice S r σ (T - t) z < K}
      = Real.exp (-r * (T - t)) *
        stdNormalCDF (-dMinus S K r σ (T - t)) := by
  have hτ : 0 < T - t := sub_pos.mpr ht
  obtain ⟨hu, hl⟩ :=
    terminalPrice_strike_events S K r σ (T - t) hS hK hσ hτ
  have hmeasure :=
    gaussianReal_halfline_probs (-dMinus S K r σ (T - t))
  constructor
  · rw [hu]
    simpa only [neg_neg] using
      congrArg (fun z : ℝ => Real.exp (-r * (T - t)) * z) hmeasure.1
  · rw [hl]
    exact congrArg (fun z : ℝ => Real.exp (-r * (T - t)) * z)
      hmeasure.2
