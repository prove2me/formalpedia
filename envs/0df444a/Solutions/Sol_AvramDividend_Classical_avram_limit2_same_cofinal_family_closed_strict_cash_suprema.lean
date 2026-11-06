-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_same_cofinal_family_closed_strict_cash_suprema
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:57:05.286616+00:00
-- url     : https://prove2.me/submissions/214fdf11-e2ae-4dbd-83a6-d92e8a7a5c84

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_arbitrary_cofinal_closed_horizon_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_limit2_arbitrary_strict_cofinal_horizon_exhaustion

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- For every cofinal possibly nonmonotone real horizon family, original
    closed and open cash suprema agree while finite endpoint atoms remain. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (T : ℕ → ℝ) (hT : ∀ a : ℝ, ∃ k : ℕ, a ≤ T k) :
    (⨆ k : ℕ,
      ∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T k),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) =
    (⨆ k : ℕ,
      ∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T k),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) := by
  have hStrict : ∀ a : ℝ, ∃ k : ℕ, a < T k := by
    intro a
    obtain ⟨k, hk⟩ := hT (a + 1)
    refine ⟨k, ?_⟩
    have ha : a < a + 1 := by linarith
    exact lt_of_lt_of_le ha hk
  calc
    _ = dividendValue X q x D :=
      (avram_limit2_arbitrary_cofinal_closed_horizon_exhaustion
        X q x D hD T hT).symm
    _ = _ :=
      avram_limit2_arbitrary_strict_cofinal_horizon_exhaustion
        X q x D hD T hStrict
