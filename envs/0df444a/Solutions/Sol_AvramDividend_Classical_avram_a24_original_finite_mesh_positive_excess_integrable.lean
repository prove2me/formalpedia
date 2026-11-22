-- Prove2me | solution 1 for AvramDividend.Classical.avram_a24_original_finite_mesh_positive_excess_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:00:57.245221+00:00
-- url     : https://prove2.me/submissions/07a7b07d-1bf3-4f18-b270-a1789929d8d5

import Mathlib
open MeasureTheory Set
open scoped BigOperators
noncomputable section

/-- A finite stopped Gaussian noise sum has integrable positive residual. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (F : Ω → ℝ) (hFI : Integrable F P)
    (a c : ℝ) (S : Finset ℕ) (G H M : ℕ → Ω → ℝ)
    (hGI : ∀ i ∈ S, Integrable (fun ω => G i ω * M i ω) P)
    (hHI : ∀ i ∈ S, Integrable (H i) P)
    (hH2I : ∀ i ∈ S, Integrable (fun ω => H i ω * (M i ω) ^ 2) P) :
    Integrable (fun ω => max (F ω - a -
      ∑ i ∈ S, (G i ω * M i ω +
      (H i ω * (M i ω) ^ 2 - c * H i ω))) 0) P:= by
  have hCell (i : ℕ) (hi : i ∈ S) :
      Integrable (fun ω => G i ω * M i ω +
        (H i ω * (M i ω) ^ 2 - c * H i ω)) P := by
    exact (hGI i hi).add ((hH2I i hi).sub ((hHI i hi).const_mul c))
  have hSum : Integrable (fun ω =>
      ∑ i ∈ S, (G i ω * M i ω +
        (H i ω * (M i ω) ^ 2 - c * H i ω))) P := by
    exact integrable_finset_sum S (fun i hi => hCell i hi)
  exact ((hFI.sub (integrable_const a)).sub hSum).pos_part
