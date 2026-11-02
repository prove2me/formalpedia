-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04b_finite_cap_actual_stopped_secant_integrable_closed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:59:29.33148+00:00
-- url     : https://prove2.me/submissions/c2e1034b-7963-440e-b03f-ab7bce72b409

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04b_finite_cap_actual_stopped_secant_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04b_cap_extension_measurable_of_zero_negative

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Finite-cap actual stopped signed dividend Stieltjes correction is
integrable without additional measurability hypotheses: the zero-negative
continuous candidate has a measurable cap-linear extension. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hCfinite : C ≠ ⊤)
    (q δ : ℝ) (hq : 0 ≤ q) (hδ : 0 ≤ δ) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T : ℝ≥0) :
    IntegrableOn (fun s : ℝ => Real.exp (-(q * s)) *
      (δ + V (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) -
        V ((x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ)))
      (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ))
      (dividendMeasure D ω) := by
  have hVmeas : Measurable V :=
    avram_wave6_04b_cap_extension_measurable_of_zero_negative
      w V C hw_cont hw_neg
      (fun htop => (hCfinite htop).elim) hVfinite
  exact avram_wave6_04b_finite_cap_actual_stopped_secant_integrable
    X x C hC hCfinite q δ hq hδ w V hw_cont hw_smooth hw_grad
    hVmeas hVfinite D hD ω T
