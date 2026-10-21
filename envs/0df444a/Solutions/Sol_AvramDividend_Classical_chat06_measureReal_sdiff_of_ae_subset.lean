-- Prove2me | solution 1 for AvramDividend.Classical.chat06_measureReal_sdiff_of_ae_subset
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T16:02:50.20296+00:00
-- url     : https://prove2.me/submissions/bf788215-3276-4d07-af6f-308c3de6da78

import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

namespace AvramChat06

/-- Real measure of a set difference, allowing inclusion only
almost surely. This transfers Poisson arrival-cylinder formulas
from a.e. monotone exponential sample paths without demanding
every-path monotonicity of the product probability space. -/
theorem measureReal_sdiff_of_ae_subset
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hSub : ∀ᵐ ω ∂P, ω ∈ A → ω ∈ B) :
    P.real (B \ A) = P.real B - P.real A := by
  have hBA : B \ (A ∩ B) = B \ A := by
    ext ω
    simp
  have hAE : (fun ω : Ω => ω ∈ A ∩ B) =ᵐ[P]
      (fun ω : Ω => ω ∈ A) := by
    filter_upwards [hSub] with ω hω
    apply propext
    constructor
    · exact And.left
    · intro ha
      exact ⟨ha, hω ha⟩
  calc
    P.real (B \ A) = P.real (B \ (A ∩ B)) := by rw [hBA]
    _ = P.real B - P.real (A ∩ B) :=
      measureReal_sdiff inter_subset_right (hA.inter hB)
    _ = P.real B - P.real A := by
      have hEq : P.real (A ∩ B) = P.real A :=
        measureReal_congr hAE
      rw [hEq]

end AvramChat06

open AvramChat06

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hSub : ∀ᵐ ω ∂P, ω ∈ A → ω ∈ B) :
    P.real (B \ A) = P.real B - P.real A := by
  exact measureReal_sdiff_of_ae_subset A B hA hB hSub
