-- Prove2me | solution 1 for AvramDividend.Classical.bv_admissible_controlled_drift_residual_ae_monotone
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T22:14:03.933327+00:00
-- url     : https://prove2.me/submissions/12e38703-62f5-4ecc-a587-5048116bc703

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D) :
    ∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 =>
      (t : ℝ) * X.drift - riskProcess X x D t ω) := by
  filter_upwards [bv_drift_deficit_ae_monotone_all_times X hBV] with ω hω
  intro s t hst
  have h1 := hω hst
  have h2 : D s ω ≤ D t ω := hD.1.2.1 ω hst
  simp only [riskProcess] at *
  linarith [mul_comm (s : ℝ) X.drift, mul_comm (t : ℝ) X.drift]
