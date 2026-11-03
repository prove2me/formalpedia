-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_09_legacy_bv_universal_bound_formally_refuted_conditionally
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:36:45.47399+00:00
-- url     : https://prove2.me/submissions/f43437b5-a728-47c4-95d5-528bfcf9d6c9

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_parent_bv_zero_cap_counterexample

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Conditional formal refutation of the exact legacy zero-cap BV
universal bound over all admissible candidates and capped strategies.
No existence of a Standing BV source is claimed or constructed here. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q x : ℝ) (hq : 0 < q) (hx : 0 < x) :
    ¬ (∀ (w : ℝ → ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) (T : ℝ),
      ContinuousOn w (Ici 0) →
      (∀ y < 0, w y = 0) →
      ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} →
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) →
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) →
      IsAdmissibleLe X x C D →
      (∀ ω (t : ℝ≥0), 0 < t →
        (t : ℝ≥0∞) < ruinTime X x D ω →
        0 ≤ w (riskProcess X x D t ω)) →
      0 ≤ T →
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) := by
  intro hUniversal
  obtain ⟨w, C, D, T, hCont, hNeg, hSmooth, hGen, hGrad,
    hD, hNonneg, hT, hFailure⟩ :=
    avram_wave5_04_parent_bv_zero_cap_counterexample
      X hX hBV q x hq hx
  exact hFailure
    (hUniversal w C D T hCont hNeg hSmooth hGen hGrad hD hNonneg hT)
