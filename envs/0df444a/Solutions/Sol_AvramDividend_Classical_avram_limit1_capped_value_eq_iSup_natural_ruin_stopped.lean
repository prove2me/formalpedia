-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit1_capped_value_eq_iSup_natural_ruin_stopped
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:36:45.791319+00:00
-- url     : https://prove2.me/submissions/f0b161a7-ff24-4b30-9eb2-390a337d449c

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

/-- The capped value is the supremum of original natural ruin-stopped
    rewards over actual capped admissible strategies. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (C : ℝ≥0∞) (x : ℝ) :
    valueFunctionLe X q C x =
      ⨆ D : ℝ≥0 → Ω → ℝ, ⨆ hD : IsAdmissibleLe X x C D, ⨆ n : ℕ,
        (∫⁻ ω, ∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) := by
  unfold valueFunctionLe
  refine iSup_congr fun D => ?_
  refine iSup_congr fun hD => ?_
  exact avram_wave6_10_original_dividendValue_eq_iSup_natural_ruin_stopped
    X q x D hD.1
