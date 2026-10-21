-- Prove2me | solution 1 for AvramDividend.Classical.chat06_positive_poisson_mass_ae_cylinder
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T16:04:33.177291+00:00
-- url     : https://prove2.me/submissions/0c74701d-a35e-4088-ac44-ea1c996b1255

import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

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

/-- From an almost-sure count-cylinder identity and the exact
successive Erlang survival formula, derive the positive-count
Poisson singleton probability. Requires no global pathwise
monotonicity or nonexplosion hypotheses. -/
theorem positive_poisson_mass_from_ae_cylinder
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (E A B : Set Ω) (n : ℕ) (t : ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hSub : ∀ᵐ ω ∂P, ω ∈ A → ω ∈ B)
    (hEvent : (fun ω : Ω => ω ∈ E) =ᵐ[P]
      (fun ω : Ω => ω ∈ B \ A))
    (hTailA : P.real A = Real.exp (-t) *
      ∑ j ∈ Finset.range (n + 1), t ^ j / (j.factorial : ℝ))
    (hTailB : P.real B = Real.exp (-t) *
      ∑ j ∈ Finset.range (n + 2), t ^ j / (j.factorial : ℝ)) :
    P.real E = Real.exp (-t) * t ^ (n + 1) /
      ((n + 1).factorial : ℝ) := by
  have hMeasure : P.real E = P.real (B \ A) :=
    measureReal_congr hEvent
  rw [hMeasure, measureReal_sdiff_of_ae_subset A B hA hB hSub,
    hTailB, hTailA, Finset.sum_range_succ]
  ring

end AvramChat06

open AvramChat06

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (E A B : Set Ω) (n : ℕ) (t : ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hSub : ∀ᵐ ω ∂P, ω ∈ A → ω ∈ B)
    (hEvent : (fun ω : Ω => ω ∈ E) =ᵐ[P]
      (fun ω : Ω => ω ∈ B \ A))
    (hTailA : P.real A = Real.exp (-t) *
      ∑ j ∈ Finset.range (n + 1), t ^ j / (j.factorial : ℝ))
    (hTailB : P.real B = Real.exp (-t) *
      ∑ j ∈ Finset.range (n + 2), t ^ j / (j.factorial : ℝ)) :
    P.real E = Real.exp (-t) * t ^ (n + 1) /
      ((n + 1).factorial : ℝ) := by
  exact positive_poisson_mass_from_ae_cylinder E A B n t
    hA hB hSub hEvent hTailA hTailB
