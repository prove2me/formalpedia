-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_finite_stopped_gaussian_grid_integrable_centred
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T23:46:12.406398+00:00
-- url     : https://prove2.me/submissions/3a0f8825-396e-4448-87c9-daaf47043268

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory

/-- Finite aggregation preserves integrability and centring of stopped physical Gaussian gains. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*} (s : Finset ι) (G : ι → Ω → ℝ)
    (hInt : ∀ i ∈ s, Integrable (G i) P)
    (hMean : ∀ i ∈ s, (∫ ω, G i ω ∂P) = 0) :
    Integrable (fun ω => ∑ i ∈ s, G i ω) P ∧
    (∫ ω, ∑ i ∈ s, G i ω ∂P) = 0  := by
  constructor
  · exact integrable_finset_sum s hInt
  · rw [integral_finset_sum s hInt]
    apply Finset.sum_eq_zero
    intro i hi
    exact hMean i hi
