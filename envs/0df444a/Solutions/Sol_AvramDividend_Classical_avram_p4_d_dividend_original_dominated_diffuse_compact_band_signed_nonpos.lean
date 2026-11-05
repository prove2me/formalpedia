-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_dominated_diffuse_compact_band_signed_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:47:24.731192+00:00
-- url     : https://prove2.me/submissions/dc759512-db9d-4054-bbe6-a8cbad54b637

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_dominated_diffuse_compact_band_discounted_signed_L1
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_selected_leftlimit_diffuse_gradient_integral_nonpos
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The signed original stopped diffuse dividend remainder is nonpositive
once compact interior reserve localisation provides the missing L1 bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (ν : Measure ℝ) [NullSingletonClass ν]
    (hdom : ν ≤ dividendMeasure D ω)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwgrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hSM : AEStronglyMeasurable (fun s : ℝ => Real.exp (-(q * s)) *
      (1 - deriv w (x + Function.leftLim (fun r : ℝ≥0 => X.X r ω)
        s.toNNReal - rightLimit D s.toNNReal ω)))
      (ν.restrict (paymentTimes σ ∩ Iic (T : ℝ))))
    (hstate : ∀ᵐ s ∂ν.restrict (paymentTimes σ ∩ Iic (T : ℝ)),
      x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal - rightLimit D s.toNNReal ω ∈ Icc a b) :
    (∫ s in (paymentTimes σ ∩ Iic (T : ℝ)), Real.exp (-(q * s)) *
      (1 - deriv w (x + Function.leftLim (fun r : ℝ≥0 => X.X r ω)
        s.toNNReal - rightLimit D s.toNNReal ω)) ∂ν) ≤ 0 := by
  let S : Set ℝ := paymentTimes σ ∩ Iic (T : ℝ)
  have hS : MeasurableSet S :=
    (paymentTimes_measurable σ).inter measurableSet_Iic
  have hregion : ∀ᵐ s ∂ν.restrict S,
      0 < (x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
        rightLimit D s.toNNReal ω) ∧
      ENNReal.ofReal (x + Function.leftLim (fun r : ℝ≥0 => X.X r ω)
        s.toNNReal - rightLimit D s.toNNReal ω) < C := by
    filter_upwards [hstate] with s hs
    exact hBand hs
  have hInt :=
    avram_p4_d_dividend_original_dominated_diffuse_compact_band_discounted_signed_L1
      X x D hD ω σ T ν hdom q hq C w hwC2 a b hab hBand hSM hstate
  exact avram_p4_d_dividend_original_selected_leftlimit_diffuse_gradient_integral_nonpos
    X x D ω ν S hS q w C hwgrad hregion hInt
