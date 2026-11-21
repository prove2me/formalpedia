-- Prove2me | solution 1 for AvramDividend.Classical.avram_a23_affine_expectation_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T09:07:58.955178+00:00
-- url     : https://prove2.me/submissions/9c5def3c-5f67-4eb8-a215-d3f02288854c

import Mathlib
open MeasureTheory

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (f g : Ω → ℝ) (hf : Integrable f P) (hg : Integrable g P)
    (ε L : ℝ)
    (hpoint : ∀ᵐ ω ∂P, f ω ≤ ε + L * g ω) :
    (∫ ω, f ω ∂P) ≤ ε + L * (∫ ω, g ω ∂P)  := by
  have he : Integrable (fun _ : Ω => ε) P := integrable_const ε
  have hgL : Integrable (fun ω => L * g ω) P := hg.const_mul L
  have hI := integral_mono_ae hf (he.add hgL) hpoint
  have hEq :
      (fun ω : Ω => ε + L * g ω) =
        (fun _ : Ω => ε) + (fun ω : Ω => L * g ω) := rfl
  rw [← hEq] at hI
  rw [integral_add he hgL] at hI
  rw [integral_const_mul] at hI
  simpa using hI
