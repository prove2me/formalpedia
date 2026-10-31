-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_controlled_reserve_future_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:23:53.139803+00:00
-- url     : https://prove2.me/submissions/bea5ffd9-2a7e-4d4d-9704-beb9be56d84c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_original_future_kernel_past_test

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
attribute [local instance] Classical.propDecidable

/-- The true controlled reserve at any deterministic time is measurable in
the past filtration. Its future Lévy increment kernel therefore factors
conditionally for every nonnegative measurable test, including marked jump
functionals, without assuming a Poisson realisation of the source. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (s : ℝ≥0)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (f : ℝ × (ℝ≥0 → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, (if ω ∈ A then
        f (x + X.X s ω - D s ω,
          fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω)
      else (0 : ℝ≥0∞)) ∂P) =
    (∫⁻ ω, (if ω ∈ A then
        ∫⁻ y, f (x + X.X s ω - D s ω, y)
          ∂(Measure.map (fun ζ => (fun t : ℝ≥0 => X.X t ζ)) P)
      else (0 : ℝ≥0∞)) ∂P) := by
  have hreserve : Measurable[𝓕 s] (fun ω => x + X.X s ω - D s ω) :=
    (measurable_const.add (X.adapted s)).sub (hD.2.2.2 s)
  exact avram_root29_01_original_future_kernel_past_test
    X s (fun ω => x + X.X s ω - D s ω) hreserve A hA f hf
