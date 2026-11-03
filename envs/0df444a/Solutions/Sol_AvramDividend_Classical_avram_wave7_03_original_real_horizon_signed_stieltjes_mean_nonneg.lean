-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_real_horizon_signed_stieltjes_mean_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T13:43:30.199882+00:00
-- url     : https://prove2.me/submissions/b55059d1-f5fc-4211-b04c-e7d967945fdf

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The original signed-looking real Stieltjes expected cash is nonnegative
    on precisely the full strict pre-ruin stopped payment set. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T) :
    0 ≤ (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
  apply integral_nonneg
  intro ω
  apply integral_nonneg
  intro t
  exact (Real.exp_pos (-(q * t))).le
