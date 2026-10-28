-- Prove2me | solution 1 for AvramDividend.Classical.levy_finiteStopping_shiftedPath_ae_event_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:55:05.929769+00:00
-- url     : https://prove2.me/submissions/0fa3f932-04d3-4f97-8be8-632973b0381b

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_shiftedFuturePath_sameLaw
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (hOrigMeas : Measurable (fun ω : Ω => fun t : ℝ≥0 => X.X t ω))
    (G : Set (ℝ≥0 → ℝ)) (hG : MeasurableSet G)
    (hOrig : ∀ᵐ ω ∂P, (fun t : ℝ≥0 => X.X t ω) ∈ G) :
    ∀ᵐ ω ∂P,
      (fun t : ℝ≥0 => X.X (τ ω + t) ω - X.X (τ ω) ω) ∈ G := by
  have hShiftMeas :=
    levy_finiteStopping_stoppedFuturePath_measurable X τ hstop
  have hLaw :=
    levy_finiteStopping_shiftedFuturePath_sameLaw X τ hτ
  apply (MeasureTheory.ae_map_iff hShiftMeas.aemeasurable hG).1
  rw [hLaw]
  exact (MeasureTheory.ae_map_iff hOrigMeas.aemeasurable hG).2 hOrig
