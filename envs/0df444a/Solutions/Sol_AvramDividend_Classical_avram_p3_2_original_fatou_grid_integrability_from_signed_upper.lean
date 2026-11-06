-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_fatou_grid_integrability_from_signed_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:52:57.905205+00:00
-- url     : https://prove2.me/submissions/5255e9d8-0f16-40f0-b565-c4b9b6acc483

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The signed original Lévy physical-grid upper certificate controls the
absolute grid cash when the payoff is nonnegative. Its L1 property follows;
one need not separately establish cash integrability for each grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (F M B : ℕ → Ω → ℝ)
    (hFMeas : ∀ n, Measurable (F n))
    (hFNonneg : ∀ n, 0 ≤ᵐ[P] F n)
    (hSigned : ∀ n,
      Integrable (fun ω => M n ω + B n ω) P)
    (hBound : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ w x + (M n ω + B n ω)) :
    ∀ n, Integrable (F n) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro n
  have hTop : Integrable
      (fun ω => w x + (M n ω + B n ω)) P :=
    (integrable_const (w x)).add (hSigned n)
  have hNorm : ∀ᵐ ω ∂P,
      ‖F n ω‖ ≤ w x + (M n ω + B n ω) := by
    filter_upwards [hFNonneg n, hBound n] with ω hnon hupper
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnon] using hupper
  exact hTop.mono' (hFMeas n).aestronglyMeasurable hNorm
