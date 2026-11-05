-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_diffuse_signed_norm_le_stopped_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:46:30.940348+00:00
-- url     : https://prove2.me/submissions/9388710e-9a70-4cfb-8edc-7c77486115aa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_dominated_diffuse_compact_band_signed_norm_le_mass
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_dominated_real_mass_le_cash

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The original stopped signed diffuse remainder is quantitatively bounded
by literal discounted dividend Cash under the source's compact interior band. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (ν : Measure ℝ) (hdom : ν ≤ dividendMeasure D ω)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hstate : ∀ᵐ s ∂ν.restrict (paymentTimes σ ∩ Iic (T : ℝ)),
      x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
        rightLimit D s.toNNReal ω ∈ Icc a b) :
    ∃ K : ℝ, 0 ≤ K ∧
      ‖∫ s in (paymentTimes σ ∩ Iic (T : ℝ)),
        Real.exp (-(q * s)) *
          (1 - deriv w (x + Function.leftLim (fun r : ℝ≥0 => X.X r ω)
            s.toNNReal - rightLimit D s.toNNReal ω)) ∂ν‖ ≤
        (1 + K) *
          ((∫⁻ s in paymentTimes σ ∩ Iic (T : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal /
             Real.exp (-(q * (T : ℝ)))) := by
  obtain ⟨K, hK, hnorm⟩ :=
    avram_p4_d_dividend_original_dominated_diffuse_compact_band_signed_norm_le_mass
      X x D hD ω σ T ν hdom q hq C w hwC2 a b hab hBand hstate
  refine ⟨K, hK, ?_⟩
  calc
    _ ≤ (1 + K) * ν.real (paymentTimes σ ∩ Iic (T : ℝ)) := hnorm
    _ ≤ (1 + K) *
        ((∫⁻ s in paymentTimes σ ∩ Iic (T : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal /
             Real.exp (-(q * (T : ℝ)))) :=
      mul_le_mul_of_nonneg_left
        (avram_p4_d_dividend_original_stopped_dominated_real_mass_le_cash
          D hD ω σ T ν hdom q hq) (by linarith)
