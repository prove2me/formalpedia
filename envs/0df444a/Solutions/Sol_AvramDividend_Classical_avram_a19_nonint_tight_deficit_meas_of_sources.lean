-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_nonint_tight_deficit_meas_of_sources
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:30:55.557932+00:00
-- url     : https://prove2.me/submissions/3f781dc3-590d-4192-a52a-48349c76f21d

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory
noncomputable section

/-- Original signed-source tight deficits inherit a.e. strong measurability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F M B : ℕ → Ω → ℝ) (c : ℝ)
    (hF : ∀ n, AEStronglyMeasurable (F n) P)
    (hM : ∀ n, AEStronglyMeasurable (M n) P)
    (hB : ∀ n, AEStronglyMeasurable (B n) P) :
    ∀ n, AEStronglyMeasurable
      (fun ω => max (F n ω - (c + (M n ω + B n ω))) 0) P := by
  intro n
  have hf : AEMeasurable (F n) P := (hF n).aemeasurable
  have hm : AEMeasurable (M n) P := (hM n).aemeasurable
  have hb : AEMeasurable (B n) P := (hB n).aemeasurable
  exact ((hf.sub (aemeasurable_const.add (hm.add hb))).max
    aemeasurable_const).aestronglyMeasurable
