-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_postrightpayment_reserve_closed_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:18:40.256184+00:00
-- url     : https://prove2.me/submissions/7f63f2c6-9421-4cc0-a9d2-3d70386b7aaa

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Original admissibility preserves the closed cap after the right payment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (hactive : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    0 ≤ x + X.X t ω - rightLimit D t ω ∧
      ENNReal.ofReal (x + X.X t ω - rightLimit D t ω) ≤ C := by
  have hmono : D t ω ≤ rightLimit D t ω :=
    dividendStrategy_le_rightLimit D hD.1.1 ω t
  have hpay := hD.1.2 ω t hactive
  have hprecap :
      ENNReal.ofReal (riskProcess X x D t ω) ≤ C := by
    by_cases ht : t = 0
    · subst t
      simpa [riskProcess, X.X_zero ω, hD.1.1.1 ω] using hxc
    · have htpos : (0 : ℝ≥0) < t :=
        lt_of_le_of_ne (show (0 : ℝ≥0) ≤ t from zero_le) (Ne.symm ht)
      exact hD.2 ω t htpos
  have hpostle :
      riskProcess X x D t ω - (rightLimit D t ω - D t ω) ≤
        riskProcess X x D t ω := by
    linarith
  have hpostnonneg :
      0 ≤ riskProcess X x D t ω -
        (rightLimit D t ω - D t ω) := by
    linarith
  have hstate : x + X.X t ω - rightLimit D t ω =
      riskProcess X x D t ω - (rightLimit D t ω - D t ω) := by
    simp only [riskProcess]
    ring
  rw [hstate]
  exact ⟨hpostnonneg, (ENNReal.ofReal_le_ofReal hpostle).trans hprecap⟩