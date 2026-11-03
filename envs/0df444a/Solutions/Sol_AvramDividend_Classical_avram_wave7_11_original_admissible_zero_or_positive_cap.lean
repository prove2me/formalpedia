-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_original_admissible_zero_or_positive_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:30:41.734862+00:00
-- url     : https://prove2.me/submissions/7a91b123-6616-499d-903b-1bf33c91a0ea

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_allCap_admissible_initial_capital_nonneg
import Mathlib.Data.ENNReal.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Original capped admissibility implies the cap is positive whenever the
    initial reserve is nonzero. The underlying original process is retained,
    including its probability law, filtration and dividend strategy type. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    x = 0 ∨ 0 < C := by
  have hx : 0 ≤ x :=
    avram_wave3_04_allCap_admissible_initial_capital_nonneg X x C hxc D hD
  rcases eq_or_lt_of_le hx with hz | hp
  · exact Or.inl hz.symm
  · exact Or.inr (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hp) hxc)
