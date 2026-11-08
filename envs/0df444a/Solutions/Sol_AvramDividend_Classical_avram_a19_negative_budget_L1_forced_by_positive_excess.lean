-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_negative_budget_L1_forced_by_positive_excess
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T08:31:44.412206+00:00
-- url     : https://prove2.me/submissions/ea18b9a7-c9a5-4011-914d-4e322fea1148

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

/-- The positive-excess upper tail forces L1 of a negative budget. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (F M B : Ω → ℝ) (a : ℝ)
    (hF : Integrable F P) (hM : Integrable M P)
    (hBmeas : AEStronglyMeasurable B P)
    (hBnonpos : ∀ ω, B ω ≤ 0)
    (hExcess : Integrable
      (fun ω => max (F ω - (a + (M ω + B ω))) 0) P) :
    Integrable B P := by
  let E : Ω → ℝ := fun ω => max (F ω - (a + (M ω + B ω))) 0
  have hE : Integrable E P := hExcess
  have ha : Integrable (fun _ : Ω => a) P := integrable_const a
  have hmajor : Integrable (fun ω => E ω - F ω + a + M ω) P := by
    exact ((hE.sub hF).add ha).add hM
  refine Integrable.mono' hmajor hBmeas ?_
  exact Filter.Eventually.of_forall (fun ω => by
    have hEge : F ω - (a + (M ω + B ω)) ≤ E ω :=
      le_max_left _ _
    have hnorm : ‖B ω‖ = -B ω := by
      rw [Real.norm_eq_abs, abs_of_nonpos (hBnonpos ω)]
    rw [hnorm]
    linarith)
