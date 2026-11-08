-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_comp10_positivepart_L1_of_nonnegative_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:21:48.249702+00:00
-- url     : https://prove2.me/submissions/4d4a23b9-cd65-40b3-bb8b-3952c3df3eb0

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set
noncomputable section

/-- A nonnegative deterministic shift does not enlarge the positive part
of an integrable signed difference, even on an infinite measure space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (F G : Ω → ℝ) (hF : Integrable F P) (hG : Integrable G P)
    (c : ℝ) (hc : 0 ≤ c) :
    Integrable (fun ω => max (F ω - (c + G ω)) 0) P := by
  have hDiff : Integrable (fun ω => F ω - G ω) P := hF.sub hG
  have hZero : Integrable (fun _ : Ω => (0 : ℝ)) P :=
    integrable_zero Ω ℝ P
  have hUpper : Integrable (fun ω => max (F ω - G ω) 0) P :=
    hDiff.sup hZero
  have hMeas :
      AEStronglyMeasurable (fun ω => max (F ω - (c + G ω)) 0) P := by
    exact (hF.aestronglyMeasurable.sub
      (aestronglyMeasurable_const.add hG.aestronglyMeasurable)).sup
        aestronglyMeasurable_const
  apply hUpper.mono_nonneg hMeas
  · filter_upwards [] with ω
    exact le_max_right _ _
  · filter_upwards [] with ω
    apply max_le_max
    · linarith
    · exact le_refl _
