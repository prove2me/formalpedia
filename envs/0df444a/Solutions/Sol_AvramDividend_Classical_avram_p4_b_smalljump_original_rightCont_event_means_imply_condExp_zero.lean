-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_rightCont_event_means_imply_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:09:46.763674+00:00
-- url     : https://prove2.me/submissions/f17f716c-5342-4126-b672-4559581ac604

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped ENNReal NNReal

/-- The original predictable event-by-event weighted compensation identity,
once proved, establishes conditional centring at the true right-continuous
source sigma algebra. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (V : Ω → ℝ)
    (hVint : Integrable V P)
    (hEventZero : ∀ A : Set Ω,
      MeasurableSet[𝓕.rightCont s] A →
      (∫ ω in A, V ω ∂P) = 0) :
    P[V | 𝓕.rightCont s] =ᵐ[P] 0 := by
  have hz :
      (fun _ : Ω => (0 : ℝ)) =ᵐ[P] P[V | 𝓕.rightCont s] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq
      (𝓕.rightCont.le s) hVint
    · intro A hA hfin
      exact integrableOn_zero
    · intro A hA hfin
      simpa using (hEventZero A hA).symm
    · exact aestronglyMeasurable_const
  exact hz.symm
