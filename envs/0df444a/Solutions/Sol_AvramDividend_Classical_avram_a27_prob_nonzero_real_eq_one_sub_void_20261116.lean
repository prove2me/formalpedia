-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_prob_nonzero_real_eq_one_sub_void_20261116
-- status  : ACCEPTED   (disprove)
-- author  : @garyholm
-- created : 2026-11-16T09:33:24.46325+00:00
-- url     : https://prove2.me/submissions/4a147535-e51e-4a31-a8b6-9a4121b1bcf5

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section



lemma a27_bot_measure_aux {α : Type*} (a : α) (s : Set α) (hs : s.Nonempty) :
    @Measure.dirac α ⊥ a s = 1 := by
  letI : MeasurableSpace α := ⊥
  rw [← measure_toMeasurable s]
  have hm : MeasurableSet (toMeasurable (Measure.dirac a) s) := measurableSet_toMeasurable _ _
  rcases MeasurableSpace.measurableSet_bot_iff.1 hm with h | h
  · exfalso
    obtain ⟨x, hx⟩ := hs
    have := subset_toMeasurable (Measure.dirac a) s hx
    rw [h] at this; exact this
  · rw [h]; simp

theorem solution : ¬ (∀ {Ω : Type} {E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → E) (hZ : Measurable Z) (z : E),
    (P {ω : Ω | Z ω ≠ z}).toReal =
      1 - (P {ω : Ω | Z ω = z}).toReal) := by
  intro h
  letI mΩ : MeasurableSpace Bool := ⊥
  let Z : Bool → Bool := fun b => b
  have hZ : Measurable Z := by
    intro s hs
    rcases MeasurableSpace.measurableSet_bot_iff.1 hs with h' | h'
    · rw [h']; exact MeasurableSet.empty
    · rw [h']; exact MeasurableSet.univ
  have := h (Measure.dirac true) Z hZ true
  rw [a27_bot_measure_aux _ _ ⟨false, by simp [Z]⟩,
    a27_bot_measure_aux _ _ ⟨true, by simp [Z]⟩] at this
  norm_num at this
