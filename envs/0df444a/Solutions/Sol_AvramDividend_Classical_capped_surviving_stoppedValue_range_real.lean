-- Prove2me | solution 1 for AvramDividend.Classical.capped_surviving_stoppedValue_range_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:57:09.102433+00:00
-- url     : https://prove2.me/submissions/4559152d-fe34-489e-929a-3c0b5a9fa0c6

import Mathlib.Probability.Process.Stopping
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- An extended stopped reserve on the surviving event lies in its finite real cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x B : ℝ) (hx : 0 ≤ x) (hB : 0 ≤ B)
    (C : ℝ≥0∞) (hC : C = ENNReal.ofReal B)
    (hxC : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0∞) (ω : Ω)
    (hτsurv : τ ω < ruinTime X x D ω) :
    stoppedValue (riskProcess X x D) τ ω ∈ Icc (0 : ℝ) B := by
  classical
  cases hτval : τ ω with
  | top =>
      have hfalse : (⊤ : ℝ≥0∞) < ruinTime X x D ω := by
        simpa [hτval] using hτsurv
      exact (not_lt_of_ge le_top hfalse).elim
  | coe t =>
      have hBefore : (t : ℝ≥0∞) < ruinTime X x D ω := by
        simpa [hτval] using hτsurv
      obtain ⟨hpos, hcap⟩ :=
        capped_riskProcess_range_before_ruin_including_zero
          X x hx C hxC D hD ω t hBefore
      have hreal : riskProcess X x D t ω ≤ B :=
        (ENNReal.ofReal_le_ofReal_iff hB).mp (by simpa [hC] using hcap)
      have hTime : WithTop.untopA (t : ℝ≥0∞) = t := by
        exact WithTop.untopD_coe (Classical.arbitrary ℝ≥0) t
      have hRange : riskProcess X x D t ω ∈ Icc (0 : ℝ) B :=
        ⟨hpos, hreal⟩
      simpa only [stoppedValue, hτval, hTime] using hRange
