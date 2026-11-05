-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_original_strict_survival_terminal_eq_postpayment_book
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:52:34.458676+00:00
-- url     : https://prove2.me/submissions/de9eb006-3fc3-4abc-8763-cfee61e3ecdf

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Exact original strict-survival post-rightpayment terminal in canonical P3 notation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (ω : Ω) (q T : ℝ) (hT : 0 ≤ T) :
    let S : ℝ≥0 := ⟨T, hT⟩
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
       Real.exp (-(q * T)) *
         w (riskProcess X x D S ω - (rightLimit D S ω - D S ω))
     else 0) =
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
       Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω)
     else 0) := by
  dsimp only
  split_ifs
  · congr 1
    congr 1
    dsimp [riskProcess]
    ring
  · rfl
