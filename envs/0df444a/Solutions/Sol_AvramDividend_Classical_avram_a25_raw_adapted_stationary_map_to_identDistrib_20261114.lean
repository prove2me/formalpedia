-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_raw_adapted_stationary_map_to_identDistrib_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:21:36.356342+00:00
-- url     : https://prove2.me/submissions/4ac5af72-0a86-45d4-96df-dcb9bf6ddf41

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

/-- Adaptation and stationary pushforward laws imply the exact IdentDistrib field of a Levy process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (G : ℝ≥0 → Ω → ℝ)
    (hAdapt : ∀ t : ℝ≥0, Measurable[𝓕 t] (G t))
    (hLaw : ∀ s T : ℝ≥0,
      Measure.map (fun ω => G (s + T) ω - G s ω) P =
        Measure.map (G T) P) :
    ∀ s t : ℝ≥0, s ≤ t →
      IdentDistrib (fun ω => G t ω - G s ω) (G (t - s)) P P := by
  intro s t hst
  have hMeasT : Measurable (G t) :=
    (hAdapt t).mono (𝓕.le t) le_rfl
  have hMeasS : Measurable (G s) :=
    (hAdapt s).mono (𝓕.le s) le_rfl
  have hMeasD : Measurable (G (t - s)) :=
    (hAdapt (t - s)).mono (𝓕.le (t - s)) le_rfl
  have hMap : Measure.map (fun ω => G t ω - G s ω) P =
      Measure.map (G (t - s)) P := by
    simpa only [add_tsub_cancel_of_le hst] using hLaw s (t - s)
  exact ⟨(hMeasT.sub hMeasS).aemeasurable,
    hMeasD.aemeasurable, hMap⟩
