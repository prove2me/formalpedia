-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04b_finite_cap_actual_stopped_secant_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:55:53.3532+00:00
-- url     : https://prove2.me/submissions/37ff7a52-172c-45c5-94a7-92a1dcedad2f

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04b_finite_cap_actual_stopped_secant_integrable_of_aesm
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04b_original_real_clock_forward_secant_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Finite-cap actual stopped signed dividend Stieltjes correction is
integrable without any abstract measurability-of-integrand hypothesis:
real-clock measurability follows from the original source paths and V. -/
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
    (hVmeas : Measurable V)
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
  have hDstrategy : IsDividendStrategy 𝓕 D := hD.1.1
  have hFmeas : Measurable (fun s : ℝ => Real.exp (-(q * s)) *
      (δ + V (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) -
        V ((x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ))) :=
    avram_wave6_04b_original_real_clock_forward_secant_measurable
      X x D hDstrategy ω q δ V hVmeas
  have hAe : AEStronglyMeasurable
      (fun s : ℝ => Real.exp (-(q * s)) *
      (δ + V (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) -
        V ((x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ)))
      ((dividendMeasure D ω).restrict
        (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ))) :=
    hFmeas.aestronglyMeasurable
  exact avram_wave6_04b_finite_cap_actual_stopped_secant_integrable_of_aesm
    X x C hC hCfinite q δ hq hδ w V hw_cont hw_smooth hw_grad
    hVfinite D hD ω T hAe
