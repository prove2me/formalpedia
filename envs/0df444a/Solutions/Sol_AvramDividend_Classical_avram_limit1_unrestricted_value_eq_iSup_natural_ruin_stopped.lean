-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit1_unrestricted_value_eq_iSup_natural_ruin_stopped
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:37:04.589687+00:00
-- url     : https://prove2.me/submissions/95a25e08-1292-4207-bf0b-c0dd7992b70b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_dividendValue_eq_iSup_natural_ruin_stopped

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The unrestricted optimal value is an exact supremum over original
    natural ruin-stopped expected Stieltjes rewards. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ) :
    valueFunction X q x =
      ⨆ D : ℝ≥0 → Ω → ℝ, ⨆ hD : IsAdmissible X x D, ⨆ n : ℕ,
        (∫⁻ ω, ∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) := by
  unfold valueFunction
  refine iSup_congr fun D => ?_
  refine iSup_congr fun hD => ?_
  exact avram_wave6_10_original_dividendValue_eq_iSup_natural_ruin_stopped
    X q x D hD
