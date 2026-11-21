-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_gaussian_bounded_cell_linear_square_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:32:52.823604+00:00
-- url     : https://prove2.me/submissions/dbcf576b-578f-4ab0-9083-0287ccb3d8e7

import Mathlib
open MeasureTheory

/-- Predictably measurable bounded original Gaussian grid Taylor coefficients give all three necessary L1 cell integrability hypotheses. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {ι : Type*} (S : Finset ι) (M G H : ι → Ω → ℝ)
    (BG BH : ι → ℝ)
    (hMI : ∀ i ∈ S, Integrable (M i) P)
    (hM2 : ∀ i ∈ S, Integrable (fun ω => (M i ω) ^ 2) P)
    (hGAE : ∀ i ∈ S, AEStronglyMeasurable (G i) P)
    (hHAE : ∀ i ∈ S, AEStronglyMeasurable (H i) P)
    (hGB : ∀ i ∈ S, ∀ᵐ ω ∂P, ‖G i ω‖ ≤ BG i)
    (hHB : ∀ i ∈ S, ∀ᵐ ω ∂P, ‖H i ω‖ ≤ BH i) :
    (∀ i ∈ S, Integrable (fun ω => G i ω * M i ω) P) ∧
    (∀ i ∈ S, Integrable (H i) P) ∧
    (∀ i ∈ S, Integrable (fun ω => H i ω * (M i ω) ^ 2) P)  := by
  constructor
  · intro i hi
    exact (hMI i hi).bdd_mul (hGAE i hi) (hGB i hi)
  constructor
  · intro i hi
    have hOne : Integrable (fun _ : Ω => (1 : ℝ)) P :=
      integrable_const 1
    have hBounded : Integrable (fun ω => H i ω * (1 : ℝ)) P :=
      hOne.bdd_mul (hHAE i hi) (hHB i hi)
    simpa only [mul_one] using hBounded
  · intro i hi
    exact (hM2 i hi).bdd_mul (hHAE i hi) (hHB i hi)
