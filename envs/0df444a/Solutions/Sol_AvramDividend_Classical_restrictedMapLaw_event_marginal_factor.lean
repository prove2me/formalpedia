-- Prove2me | solution 1 for AvramDividend.Classical.restrictedMapLaw_event_marginal_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:04:02.919991+00:00
-- url     : https://prove2.me/submissions/cb1900b4-55da-479a-9dc7-6f092d0eb7ea

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.MeasureSpace

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- A restricted pushforward law yields event-marginal factorisation. -/
theorem solution

    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : Measure Ω) (Y : Ω → β) (hY : Measurable Y)
    (A : Set Ω)
    (hLaw : Measure.map Y (P.restrict A) =
      (P A) • Measure.map Y P)
    (B : Set β) (hB : MeasurableSet B) :
    P (A ∩ Y ⁻¹' B) = P A * P (Y ⁻¹' B) := by
  have hPre : MeasurableSet (Y ⁻¹' B) := hB.preimage hY
  calc
    P (A ∩ Y ⁻¹' B) = (P.restrict A) (Y ⁻¹' B) := by
      rw [Measure.restrict_apply hPre, Set.inter_comm]
    _ = (Measure.map Y (P.restrict A)) B :=
      (Measure.map_apply hY hB).symm
    _ = ((P A) • Measure.map Y P) B :=
      congrArg (fun μ : Measure β => μ B) hLaw
    _ = P A * P (Y ⁻¹' B) := by
      rw [Measure.smul_apply, Measure.map_apply hY hB]
      exact smul_eq_mul _ _
