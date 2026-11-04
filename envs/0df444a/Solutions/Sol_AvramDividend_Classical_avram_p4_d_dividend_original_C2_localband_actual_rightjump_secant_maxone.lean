-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_C2_localband_actual_rightjump_secant_maxone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:49:17.9962+00:00
-- url     : https://prove2.me/submissions/854637ba-5747-4695-8ae0-3b193ef7090c

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_ubv_C2_interior_band_secant_lipschitz
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Interior source C² regularity bounds the actual post-source right-payment secant. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (K : ℝ≥0) (hK : ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ K)
    (ω : Ω) (t : ℝ≥0)
    (hPre : riskProcess X x D t ω ∈ Icc a b)
    (hPost : x + X.X t ω - rightLimit D t ω ∈ Icc a b) :
    w (riskProcess X x D t ω) -
      w (x + X.X t ω - rightLimit D t ω) ≤
      max 1 (K : ℝ) * (rightLimit D t ω - D t ω) := by
  have hDelta : 0 ≤ rightLimit D t ω - D t ω :=
    sub_nonneg.mpr (dividendStrategy_le_rightLimit D hD ω t)
  have hDifference :
      riskProcess X x D t ω - (x + X.X t ω - rightLimit D t ω) =
        rightLimit D t ω - D t ω := by
    simp only [riskProcess]
    ring
  have hLip := avram_p4_d_dividend_ubv_C2_interior_band_secant_lipschitz
    C w hwC2 a b hOpen hBand K hK
    (riskProcess X x D t ω) hPre
    (x + X.X t ω - rightLimit D t ω) hPost
  have hAbs :
      |riskProcess X x D t ω - (x + X.X t ω - rightLimit D t ω)| =
        rightLimit D t ω - D t ω := by
    rw [hDifference, abs_of_nonneg hDelta]
  calc
    w (riskProcess X x D t ω) - w (x + X.X t ω - rightLimit D t ω) ≤
        |w (riskProcess X x D t ω) - w (x + X.X t ω - rightLimit D t ω)| :=
      le_abs_self _
    _ ≤ (K : ℝ) * |riskProcess X x D t ω -
        (x + X.X t ω - rightLimit D t ω)| := hLip
    _ = (K : ℝ) * (rightLimit D t ω - D t ω) := by rw [hAbs]
    _ ≤ max 1 (K : ℝ) * (rightLimit D t ω - D t ω) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hDelta
