-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_original_preruin_interval_full_dividend_measure_signed_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:31:07.589073+00:00
-- url     : https://prove2.me/submissions/08ead8c7-97a3-4dd1-9d69-29e5f3e4a253

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_interval_signed_stieltjes_control_nonpos

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The original full Stieltjes dividend cell mass is bounded by the true source-frozen signed cap-linear value drop. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (hV : ∀ z : ℝ, V z = if z ≤ c then w z else w c + (z - c))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b)
    (hPre : b = 0 ∨ (b : ℝ≥0∞) < ruinTime X x D ω) :
    (dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ))).toReal +
      V (x + X.X b ω - rightLimit D b ω) -
      V (x + X.X b ω - rightLimit D a ω) ≤ 0 := by
  have hSigned := avram_wave5_04b_original_preruin_interval_signed_stieltjes_control_nonpos
    X x c hc (0 : ℝ) (le_refl 0) w V hw_cont hw_smooth hw_grad hV
    D hD ω a b hab hPre
  simpa [MeasureTheory.lintegral_const] using hSigned
