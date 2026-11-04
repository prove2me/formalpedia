-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_local_right_remainder_lipschitz_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:24:20.528489+00:00
-- url     : https://prove2.me/submissions/e1e4c943-7441-4b51-8b14-780ddb8dc954

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
/-- A local derivative ceiling bounds the exact signed right-payment error. -/
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
    |(rightLimit D t ω - D t ω) +
      w (x + X.X t ω - rightLimit D t ω) - w (riskProcess X x D t ω)| ≤
      (1 + (L : ℝ)) * (rightLimit D t ω - D t ω) := by
  have hmono : D t ω ≤ rightLimit D t ω :=
    dividendStrategy_le_rightLimit D hD ω t
  have hδ : 0 ≤ rightLimit D t ω - D t ω := sub_nonneg.mpr hmono
  have hstate : x + X.X t ω - rightLimit D t ω =
      riskProcess X x D t ω - (rightLimit D t ω - D t ω) := by
    simp only [riskProcess]
    ring
  have hgap : |(x + X.X t ω - rightLimit D t ω) - (riskProcess X x D t ω)| =
      (rightLimit D t ω - D t ω) := by
    have heq : (x + X.X t ω - rightLimit D t ω) - (riskProcess X x D t ω) =
        -(rightLimit D t ω - D t ω) := by rw [hstate]; ring
    rw [heq, abs_neg, abs_of_nonneg hδ]
  have hLip :=
    avram_wave8_22_original_BV_compact_derivative_implies_lipschitz
      w a b L hDiff hDeriv (x + X.X t ω - rightLimit D t ω) hpost
      (riskProcess X x D t ω) hpre
  rw [hgap] at hLip
  calc
    |(rightLimit D t ω - D t ω) + w (x + X.X t ω - rightLimit D t ω) -
        w (riskProcess X x D t ω)| =
      |(rightLimit D t ω - D t ω) + (w (x + X.X t ω - rightLimit D t ω) -
        w (riskProcess X x D t ω))| := by ring
    _ ≤ |(rightLimit D t ω - D t ω)| +
      |w (x + X.X t ω - rightLimit D t ω) - w (riskProcess X x D t ω)| := abs_add_le _ _
    _ ≤ (rightLimit D t ω - D t ω) + (L : ℝ) * (rightLimit D t ω - D t ω) := by
      simpa [abs_of_nonneg hδ] using add_le_add_left hLip (rightLimit D t ω - D t ω)
    _ = (1 + (L : ℝ)) * (rightLimit D t ω - D t ω) := by ring
