-- Prove2me | solution 1 for AvramDividend.Classical.stopped_discounted_drift_tail_layercake
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:42:58.255221+00:00
-- url     : https://prove2.me/submissions/d4c83dc6-ed5d-40dc-a688-b5aea211ef46

import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FunProp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Expected discounted drift paid up to a nonnegative real stopping clock
equals its time-integral weighted by strict survival probability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (τ : Ω → ℝ) (hτ : Measurable τ)
    (hNonneg : ∀ᵐ ω ∂P, 0 ≤ τ ω)
    (d q : ℝ) (hd : 0 ≤ d) :
    (∫⁻ ω, ENNReal.ofReal
        (∫ t in (0 : ℝ)..τ ω, d * Real.exp (-(q * t))) ∂P) =
      ∫⁻ t in Ioi (0 : ℝ),
        P {ω : Ω | t < τ ω} *
          ENNReal.ofReal (d * Real.exp (-(q * t))) := by
  apply lintegral_comp_eq_lintegral_meas_lt_mul P hNonneg hτ.aemeasurable
  · intro t ht
    have hcont : Continuous (fun s : ℝ => d * Real.exp (-(q * s))) := by
      fun_prop
    exact hcont.intervalIntegrable 0 t
  · exact Filter.Eventually.of_forall (fun t =>
      mul_nonneg hd (Real.exp_nonneg _))
