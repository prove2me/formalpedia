-- Prove2me | solution 1 for AvramDividend.Classical.chat06_history_comap_prefix_representation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:07:43.632865+00:00
-- url     : https://prove2.me/submissions/4d4e8eee-9d10-4124-9688-a97834ab8c77

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.MeasureSpace

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- A complete observed history that factors through a finite-prefix
variable on the count cylinder has the same measurable events there.
The history event is measured in its natural comap sigma-algebra. -/
theorem solution
    {Ω A E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSpace E]
    (P : Measure Ω) (N : Ω → ℕ) (n : ℕ)
    (Z : Ω → A) (path : Ω → E) (φ : A → E)
    (hφ : Measurable φ)
    (hPath : ∀ᵐ ω ∂P, N ω = n → path ω = φ (Z ω))
    (H : Set Ω)
    (hH : MeasurableSet[
      MeasurableSpace.comap path (inferInstance : MeasurableSpace E)] H) :
    ∃ Q : Set A, MeasurableSet Q ∧
      (fun ω : Ω => ω ∈ H ∧ N ω = n) =ᵐ[P]
        (fun ω : Ω => Z ω ∈ Q ∧ N ω = n) := by
  obtain ⟨B, hB, hPre⟩ :=
    (MeasurableSpace.measurableSet_comap).mp hH
  refine ⟨φ ⁻¹' B, hφ hB, ?_⟩
  filter_upwards [hPath] with ω hω
  apply propext
  constructor
  · rintro ⟨hh, hn⟩
    have hb : path ω ∈ B := by
      have hm : ω ∈ path ⁻¹' B := by
        rw [hPre]
        exact hh
      exact hm
    rw [hω hn] at hb
    exact ⟨hb, hn⟩
  · rintro ⟨hq, hn⟩
    have hb : path ω ∈ B := by
      rw [hω hn]
      exact hq
    have hh : ω ∈ H := by
      rw [← hPre]
      exact hb
    exact ⟨hh, hn⟩
