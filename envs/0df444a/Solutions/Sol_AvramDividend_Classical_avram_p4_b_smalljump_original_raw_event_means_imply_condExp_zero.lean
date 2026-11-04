-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_raw_event_means_imply_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:09:58.563304+00:00
-- url     : https://prove2.me/submissions/f0c471b9-e24b-48d3-af77-0d1f5ab8620b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped ENNReal NNReal

/-- Exact raw-filtration conditional-centering bridge from P2's original
predictable-rectangle event-by-event compensated jump identities. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (V : Ω → ℝ)
    (hVint : Integrable V P)
    (hEventZero : ∀ A : Set Ω,
      MeasurableSet[𝓕 s] A →
      (∫ ω in A, V ω ∂P) = 0) :
    P[V | 𝓕 s] =ᵐ[P] 0 := by
  have hz :
      (fun _ : Ω => (0 : ℝ)) =ᵐ[P] P[V | 𝓕 s] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq
      (𝓕.le s) hVint
    · intro A hA hfin
      exact integrableOn_zero
    · intro A hA hfin
      simpa using (hEventZero A hA).symm
    · exact aestronglyMeasurable_const
  exact hz.symm
