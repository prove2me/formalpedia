-- Prove2me | solution 1 for AvramDividend.Classical.capped_riskProcess_range_before_ruin_including_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:03:21.346934+00:00
-- url     : https://prove2.me/submissions/56f6d1c7-d168-457f-b2d4-ce4e067554e0

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The controlled reserve lies in the verification domain, even at time zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 ≤ x)
    (C : ℝ≥0∞) (hxC : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < ruinTime X x D ω) :
    0 ≤ riskProcess X x D t ω ∧
      ENNReal.ofReal (riskProcess X x D t ω) ≤ C := by
  by_cases hzero : t = 0
  · subst t
    have hD0 : D 0 ω = 0 := hD.1.1.1 ω
    have hX0 : X.X 0 ω = 0 := X.X_zero ω
    simpa [riskProcess, hX0, hD0] using (And.intro hx hxC)
  · have hpos : 0 < t := pos_iff_ne_zero.mpr hzero
    exact ⟨riskProcess_nonneg_before_ruin X x D ω t ht,
      hD.2 ω t hpos⟩
