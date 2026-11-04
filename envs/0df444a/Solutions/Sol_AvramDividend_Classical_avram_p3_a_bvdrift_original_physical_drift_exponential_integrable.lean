-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_physical_drift_exponential_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:29:04.954055+00:00
-- url     : https://prove2.me/submissions/cf9a2694-6d6c-489c-9ac6-1e6a66fa111c

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original finite-horizon Levy Laplace law integrates the genuine
physical-drift-normalised exponential, including heavy negative tails. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω : Ω =>
      Real.exp (θ * (X.X T ω - (T : ℝ) * X.drift))) P := by
  have hLap := (X.laplace T θ hθ).1
  have hEq :
      (fun ω : Ω =>
        Real.exp (θ * (X.X T ω - (T : ℝ) * X.drift))) =
      (fun ω : Ω =>
        Real.exp (-(θ * (T : ℝ) * X.drift)) *
          Real.exp (θ * X.X T ω)) := by
    funext ω
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hEq]
  exact hLap.const_mul _
