-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger23_original_samegrid_prepost_gradient_jump_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T13:24:02.696541+00:00
-- url     : https://prove2.me/submissions/5e610e9a-7b60-45e9-a572-eb3adbd23c66

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ubv_C2_interior_band_gradient_lipschitz

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original prepayment/postpayment gradient coefficients differ by the right dividend jump. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (K : ℝ≥0)
    (hK : ∀ y ∈ Icc a b, ‖deriv (deriv w) y‖₊ ≤ K)
    (s : ℝ≥0) (ω : Ω)
    (hPre : riskProcess X x D s ω ∈ Icc a b)
    (hPost : x + X.X s ω - rightLimit D s ω ∈ Icc a b)
    (hRight : 0 ≤ rightLimit D s ω - D s ω) :
    |deriv w (riskProcess X x D s ω) -
      deriv w (x + X.X s ω - rightLimit D s ω)| ≤
        (K : ℝ) * (rightLimit D s ω - D s ω) := by
  have hLip :=
    avram_p4_a_gaussian_ubv_C2_interior_band_gradient_lipschitz
      C w hw a b hOpen hBand K hK
      (riskProcess X x D s ω) hPre
      (x + X.X s ω - rightLimit D s ω) hPost
  have hDiff : riskProcess X x D s ω -
      (x + X.X s ω - rightLimit D s ω) =
        rightLimit D s ω - D s ω := by
    simp only [riskProcess]
    ring
  calc
    _ ≤ (K : ℝ) *
        |riskProcess X x D s ω -
          (x + X.X s ω - rightLimit D s ω)| := hLip
    _ = (K : ℝ) * (rightLimit D s ω - D s ω) := by
      rw [hDiff, abs_of_nonneg hRight]
