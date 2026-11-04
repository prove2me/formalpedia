-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_ubv_sigma_zero_original_stopped_second_order_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:50:31.177085+00:00
-- url     : https://prove2.me/submissions/ff6f7848-71c1-4f2e-bd68-c21e1c1b6582

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original controlled pure-jump UBV Gaussian correction is zero,
for any explicit time measure on any stopped interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (_hUBV : ¬ X.BoundedVariation)
    (hZero : X.σ = 0)
    (q : ℝ) (w : ℝ → ℝ) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0)
    (μ : Measure ℝ≥0) (ω : Ω) :
    IntegrableOn
      (fun s : ℝ≥0 => Real.exp (-(q * (s : ℝ))) *
        (X.σ ^ 2 / 2 * iteratedDeriv 2 w (riskProcess X x D s ω)))
      (Icc 0 (τ ω)) μ ∧
    (∫ s in Icc 0 (τ ω), Real.exp (-(q * (s : ℝ))) *
      (X.σ ^ 2 / 2 * iteratedDeriv 2 w (riskProcess X x D s ω)) ∂μ) = 0 := by
  constructor <;> simp [hZero]
