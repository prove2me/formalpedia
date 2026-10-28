-- Prove2me | solution 2 for AvramDividend.Classical.zero_integral_positive_deficit_event_null
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:11:40.012232+00:00
-- url     : https://prove2.me/submissions/c3e254f6-13db-47cf-b095-1bcd98c1f145

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.Measure.Restrict

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
    · simp [indicator_of_mem h, hω]
    · simp [indicator_of_notMem h]
  have h0 : E.indicator D =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnn hIntegrable).1 hIntegral
  have hsub : E ⊆ {ω | D ω = 0} ∪ {ω | E.indicator D ω ≠ 0} := by
    intro ω hω
    by_cases h : D ω = 0
    · exact Or.inl h
    · right; simp [h, hω]
  have hnull : P {ω | E.indicator D ω ≠ 0} = 0 := by
    have := h0
    rw [Filter.EventuallyEq, ae_iff] at this
    simpa using this
  exact measure_mono_null hsub (measure_union_null hAtom hnull)
