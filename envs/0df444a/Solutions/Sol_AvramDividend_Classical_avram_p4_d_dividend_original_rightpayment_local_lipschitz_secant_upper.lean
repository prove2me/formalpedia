-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_rightpayment_local_lipschitz_secant_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T19:57:43.504045+00:00
-- url     : https://prove2.me/submissions/1c3cb9a2-74d6-4f5e-b68c-a165cf303a19

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_compact_derivative_implies_lipschitz

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- An honestly localised C1 reserve-band Lipschitz constant gives the
secant upper bound at the original post-X and pre-right-D payment reserves. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b : ℝ) (L : ℝ≥0)
    (hDiff : ∀ y ∈ Icc a b, DifferentiableAt ℝ w y)
    (hDeriv : ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ L)
    (ω : Ω) (t : ℝ≥0)
    (hpre : riskProcess X x D t ω ∈ Icc a b)
    (hpost : x + X.X t ω - rightLimit D t ω ∈ Icc a b) :
    w (riskProcess X x D t ω) -
      w (x + X.X t ω - rightLimit D t ω) ≤
        (1 + (L : ℝ)) * (rightLimit D t ω - D t ω) := by
  have hmono : D t ω ≤ rightLimit D t ω :=
    dividendStrategy_le_rightLimit D hD ω t
  have hδ : 0 ≤ rightLimit D t ω - D t ω := sub_nonneg.mpr hmono
  have hstate : x + X.X t ω - rightLimit D t ω =
      riskProcess X x D t ω - (rightLimit D t ω - D t ω) := by
    simp only [riskProcess]
    ring
  have hgap : |riskProcess X x D t ω -
      (x + X.X t ω - rightLimit D t ω)| =
      rightLimit D t ω - D t ω := by
    rw [hstate]
    simp [abs_of_nonneg hδ]
  have hLip :=
    avram_wave8_22_original_BV_compact_derivative_implies_lipschitz
      w a b L hDiff hDeriv (riskProcess X x D t ω) hpre
      (x + X.X t ω - rightLimit D t ω) hpost
  rw [hgap] at hLip
  calc
    w (riskProcess X x D t ω) - w (x + X.X t ω - rightLimit D t ω) ≤
        |w (riskProcess X x D t ω) - w (x + X.X t ω - rightLimit D t ω)| :=
      le_abs_self _
    _ ≤ (L : ℝ) * (rightLimit D t ω - D t ω) := hLip
    _ ≤ (1 + (L : ℝ)) * (rightLimit D t ω - D t ω) := by
      nlinarith
