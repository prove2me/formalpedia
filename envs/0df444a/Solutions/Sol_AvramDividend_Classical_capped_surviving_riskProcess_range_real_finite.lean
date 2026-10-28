-- Prove2me | solution 1 for AvramDividend.Classical.capped_surviving_riskProcess_range_real_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:01:38.069834+00:00
-- url     : https://prove2.me/submissions/bc2a37e4-7b1b-4a88-b562-2a3578e9b995

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The finite-time controlled reserve stays in its real cap strictly before ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x B : ℝ) (hx : 0 ≤ x) (hB : 0 ≤ B)
    (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal B)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal B) D)
    (ω : Ω) (t : ℝ≥0)
    (hBefore : (t : ℝ≥0∞) < ruinTime X x D ω) :
    riskProcess X x D t ω ∈ Icc (0 : ℝ) B := by
  obtain ⟨hpos, hcap⟩ :=
    capped_riskProcess_range_before_ruin_including_zero
      X x hx (ENNReal.ofReal B) hxc D hD ω t hBefore
  exact ⟨hpos, (ENNReal.ofReal_le_ofReal_iff hB).mp hcap⟩
