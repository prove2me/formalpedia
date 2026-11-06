-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_strict_preruin_prepayment_reserve_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T21:56:05.204205+00:00
-- url     : https://prove2.me/submissions/3fb3bb43-d5db-46ab-8e67-e0fe579b7396

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Under original capped admissibility the actual pre-rightpayment reserve
at zero or strictly before ruin is nonnegative, including at cap contact. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    0 ≤ riskProcess X x D t ω := by
  have hAfter := hD.1.2 ω t ht
  have hBefore := dividendStrategy_le_rightLimit D hD.1.1 ω t
  dsimp [riskProcess] at *
  linarith
