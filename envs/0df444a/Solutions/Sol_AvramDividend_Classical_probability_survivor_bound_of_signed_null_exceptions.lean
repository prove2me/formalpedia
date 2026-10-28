-- Prove2me | solution 1 for AvramDividend.Classical.probability_survivor_bound_of_signed_null_exceptions
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T16:26:50.80898+00:00
-- url     : https://prove2.me/submissions/b30ea16b-eeb0-4d5d-a732-6627c73e0a3e

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
open MeasureTheory Set
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A survivor event is controlled by its zero-deficit atom when its
positive and negative-deficit exceptions have zero probability. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (D : Ω → ℝ)
    (hPos : P.real {ω : Ω | ω ∈ A ∧ 0 < D ω} = 0)
    (hNeg : P.real {ω : Ω | D ω < 0} = 0) :
    P.real A ≤ P.real {ω : Ω | D ω = 0} := by
  let E : Set Ω := {ω | D ω = 0}
  let F : Set Ω := {ω | ω ∈ A ∧ 0 < D ω}
  let G : Set Ω := {ω | D ω < 0}
  have hSub : A ⊆ E ∪ (F ∪ G) := by
    intro ω hω
    rcases lt_trichotomy (D ω) 0 with hn | he | hp
    · exact Or.inr (Or.inr hn)
    · exact Or.inl he
    · exact Or.inr (Or.inl ⟨hω, hp⟩)
  have hF : P.real F = 0 := hPos
  have hG : P.real G = 0 := hNeg
  calc
    P.real A ≤ P.real (E ∪ (F ∪ G)) := measureReal_mono hSub
    _ ≤ P.real E + P.real (F ∪ G) := measureReal_union_le E (F ∪ G)
    _ ≤ P.real E + (P.real F + P.real G) := by
      simpa only [add_comm] using
        (add_le_add_left (measureReal_union_le F G) (P.real E))
    _ = P.real E := by simp [hF, hG]
