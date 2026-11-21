-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_original_strict_preruin_right_dividends_le_initial_plus_true_Levy_runningSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:51:21.108707+00:00
-- url     : https://prove2.me/submissions/fd6a18ef-72de-4e1f-84c9-826e700481d9

import Mathlib
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_nonnegative_strictly_before_ruin
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (t : ℝ≥0) (ω : Ω)
    (ht : (t : ℝ≥0∞) < ruinTime X x D ω) :
    rightLimit D t ω ≤ x + runningSup X t ω := by
  have hRes :
      0 ≤ x + X.X t ω - rightLimit D t ω :=
    postPaymentReserve_nonnegative_strictly_before_ruin
      X x D hD ω t ht
  have hSup : X.X t ω ≤ runningSup X t ω :=
    (runningSup_monotone_and_path_le X ω).2 t
  linarith
