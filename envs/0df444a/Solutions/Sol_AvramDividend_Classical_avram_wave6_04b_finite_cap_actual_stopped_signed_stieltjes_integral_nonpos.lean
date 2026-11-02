-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04b_finite_cap_actual_stopped_signed_stieltjes_integral_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T20:07:26.136872+00:00
-- url     : https://prove2.me/submissions/0bc7fce9-34e9-4f6d-a25b-3078fb30945f

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04b_finite_cap_actual_stopped_secant_integrable_closed
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04b_allcap_actual_real_clock_forward_secant_nonpos
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The exact original stopped actual dividend Stieltjes integral is a
genuine finite signed integral and is nonpositive on the full payment set,
including the zero atom, singular-continuous variation and all cap contacts. -/
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
      (dividendMeasure D ω) ∧
    (∫ s : ℝ, Real.exp (-(q * s)) *
      (δ + V (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) -
        V ((x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ))
        ∂((dividendMeasure D ω).restrict
          (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ)))) ≤ 0 := by
  constructor
  · exact avram_wave6_04b_finite_cap_actual_stopped_secant_integrable_closed
      X x C hC hCfinite q δ hq hδ w V hw_cont hw_smooth hw_grad
      hw_neg hVfinite D hD ω T
  · have hAmeas : MeasurableSet
        (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ)) :=
      (paymentTimes_measurable _).inter measurableSet_Icc
    have hVtop : C = ⊤ → ∀ y : ℝ, V y = w y :=
      fun htop => (hCfinite htop).elim
    apply integral_nonpos_of_ae
    filter_upwards [ae_restrict_mem hAmeas] with s hs
    exact avram_wave6_04b_allcap_actual_real_clock_forward_secant_nonpos
      X x C hC q δ hδ w V hw_cont hw_smooth hw_grad
      hVtop hVfinite D hD ω s hs.1
