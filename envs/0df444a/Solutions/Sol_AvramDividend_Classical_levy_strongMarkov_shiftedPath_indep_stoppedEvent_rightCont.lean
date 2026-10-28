-- Prove2me | solution 1 for AvramDividend.Classical.levy_strongMarkov_shiftedPath_indep_stoppedEvent_rightCont
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:55:55.526778+00:00
-- url     : https://prove2.me/submissions/58959fc6-8f9f-4315-8b80-0e450f86ab36

import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Independence.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_levy_strongMarkov_shiftedPath_indep_stoppedEvent

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    Measure.map
      (fun ω : Ω =>
        (Set.indicator A (fun _ : Ω => (1 : ℝ)) ω,
          fun t : ℝ≥0 => X.X (τ ω + t) ω - X.X (τ ω) ω)) P =
      (Measure.map (Set.indicator A (fun _ : Ω => (1 : ℝ))) P).prod
        (Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P) := by
  obtain ⟨Y, hY, _, _, _⟩ := levy_rightCont_process X
  have h := levy_strongMarkov_shiftedPath_indep_stoppedEvent Y τ hτ A hA
  simpa only [hY] using h
