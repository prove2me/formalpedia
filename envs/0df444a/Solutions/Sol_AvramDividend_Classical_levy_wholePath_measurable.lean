-- Prove2me | solution 1 for AvramDividend.Classical.levy_wholePath_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:34:44.750217+00:00
-- url     : https://prove2.me/submissions/20d34b8a-4bee-4572-a70c-7455d91a3e1a

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Measurable (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) := by
  have hstop : IsStoppingTime 𝓕
      (fun _ : Ω => (0 : WithTop ℝ≥0)) := by
    intro t
    simp
  have hwhole := levy_finiteStopping_stoppedFuturePath_measurable
    X (fun _ : Ω => (0 : ℝ≥0)) hstop
  simpa [X.X_zero] using hwhole
