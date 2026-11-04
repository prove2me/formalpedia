-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_fourth_weight_real_lintegral_identification
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:33:49.119392+00:00
-- url     : https://prove2.me/submissions/fcf13ec0-1371-421f-aa57-3247a353b4aa

import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : Ω → ℝ) (θ : ℝ)
    (hInt : Integrable
      (fun ω => (Real.exp (θ * Y ω) - 1) ^ 4) μ) :
    ENNReal.ofReal
      (∫ ω, (Real.exp (θ * Y ω) - 1) ^ 4 ∂μ) =
    ∫⁻ ω, ENNReal.ofReal
      ((Real.exp (θ * Y ω) - 1) ^ 4) ∂μ := by
  have hnon : ∀ᵐ ω ∂μ,
      0 ≤ (Real.exp (θ * Y ω) - 1) ^ 4 :=
    Filter.Eventually.of_forall (fun ω => by positivity)
  exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnon