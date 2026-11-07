-- Prove2me | solution 1 for AvramDividend.Classical.avram_route10_signed_integrable_nonpositive_mean_centering
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T14:48:28.88109+00:00
-- url     : https://prove2.me/submissions/3db21e86-49f5-4c5e-8737-4748139cb926

import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : Integrable Z P)
    (hMean : (∫ ω, Z ω ∂P) ≤ 0) :
    ∃ M B : Ω → ℝ,
      Integrable M P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ ω, B ω ≤ 0) ∧
      (∀ ω, Z ω = M ω + B ω) := by
  let b : ℝ := ∫ ω, Z ω ∂P
  refine ⟨(fun ω => Z ω - b), (fun _ => b), ?_, ?_, ?_, ?_⟩
  · exact hZ.sub (integrable_const b)
  · rw [integral_sub hZ (integrable_const b)]
    simp [b]
  · intro ω
    simpa only [b] using hMean
  · intro ω
    ring
