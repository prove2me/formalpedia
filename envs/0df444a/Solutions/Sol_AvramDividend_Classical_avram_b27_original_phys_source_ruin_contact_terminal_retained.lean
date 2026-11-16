-- Prove2me | solution 1 for AvramDividend.Classical.avram_b27_original_phys_source_ruin_contact_terminal_retained
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:55:13.001084+00:00
-- url     : https://prove2.me/submissions/e15369e9-9a75-4a0b-8e47-9cda137fd31c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (σ : Ω → ℝ≥0) (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨
              (σ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ ω) ω - rightLimit D (σ ω) ω
          else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (ω : Ω) (hσ : 0 < σ ω)
    (hContact : (σ ω : ℝ≥0∞) = ruinTime X x D ω)
    (hReserve : riskProcess X x D (σ ω) ω = 0)
    (hw0 : w 0 = 1)
    (hZeroCash :
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal = 0) :
    F ω = Real.exp (-(q * (σ ω : ℝ))) := by
  have hσ0 : σ ω ≠ 0 := ne_of_gt hσ
  have hNotBefore :
      ¬ ((σ ω : ℝ≥0∞) < ruinTime X x D ω) := by
    rw [← hContact]
    exact lt_irrefl _
  have hNotBranch :
      ¬ (σ ω = 0 ∨ (σ ω : ℝ≥0∞) < ruinTime X x D ω) :=
    not_or_intro hσ0 hNotBefore
  rw [hFsource ω]
  simp [hNotBranch, hReserve, hw0, hZeroCash]
