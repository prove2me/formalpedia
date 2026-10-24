-- Prove2me | solution 1 for AvramDividend.Classical.capped_surviving_riskProcess_expected_le_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:05:06.826619+00:00
-- url     : https://prove2.me/submissions/0fbc3eb1-f3c2-4780-a08b-14ba2fe6afb0

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Cap admissibility bounds the surviving controlled-reserve first moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (t : ℝ≥0) (ht : 0 < t) :
    (∫⁻ ω, if (t : ℝ≥0∞) < ruinTime X x D ω then
      ENNReal.ofReal (riskProcess X x D t ω) else 0 ∂P) ≤ C := by
  haveI : IsProbabilityMeasure P := X.isProbability
  calc
    (∫⁻ ω, if (t : ℝ≥0∞) < ruinTime X x D ω then
      ENNReal.ofReal (riskProcess X x D t ω) else 0 ∂P) ≤
      ∫⁻ _ : Ω, C ∂P := by
        apply lintegral_mono
        intro ω
        change (if (t : ℝ≥0∞) < ruinTime X x D ω then
          ENNReal.ofReal (riskProcess X x D t ω) else 0) ≤ C
        split_ifs with hSurvive
        · exact hD.2 ω t ht
        · exact bot_le
    _ = C := by simp
