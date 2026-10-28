-- Prove2me | solution 1 for AvramDividend.Classical.zero_integral_positive_deficit_event_null
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:11:22.532038+00:00
-- url     : https://prove2.me/submissions/66f4e550-1ad1-41b8-b979-3f10b77799e4

import Mathlib

open MeasureTheory Set
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (E : Set Ω) (D : Ω → ℝ)
    (hD : ∀ᵐ ω ∂P, 0 ≤ D ω)
    (hAtom : P {ω : Ω | D ω = 0} = 0)
    (hIntegrable : Integrable (E.indicator D) P)
    (hIntegral : (∫ ω, E.indicator D ω ∂P) = 0) :
    P E = 0 := by
  have hnn : 0 ≤ᵐ[P] E.indicator D := by
    filter_upwards [hD] with ω hω
    by_cases h : ω ∈ E
    · simp [h, hω]
    · simp [h]
  have h0 : E.indicator D =ᵐ[P] 0 := (integral_eq_zero_iff_of_nonneg_ae hnn hIntegrable).mp hIntegral
  have h1 : P {ω | E.indicator D ω ≠ 0} = 0 := by
    rw [← ae_iff]; exact h0
  have hsub : E ⊆ {ω | E.indicator D ω ≠ 0} ∪ {ω | D ω = 0} := by
    intro ω hω
    by_cases h : D ω = 0
    · exact Or.inr h
    · left; simp [hω, h]
  refine le_antisymm ?_ (zero_le)
  calc P E ≤ P ({ω | E.indicator D ω ≠ 0} ∪ {ω | D ω = 0}) := measure_mono hsub
    _ ≤ P {ω | E.indicator D ω ≠ 0} + P {ω | D ω = 0} := measure_union_le _ _
    _ = 0 := by rw [h1, hAtom, add_zero]
