-- Prove2me | solution 2 for AvramDividend.Classical.cross_levy_path_event_law_of_equal_psi
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T18:36:01.989223+00:00
-- url     : https://prove2.me/submissions/0dd12135-ca3f-41e4-a574-f64e5cf00c12

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Theorems.Thm_AvramDividend_Classical_cross_levy_whole_path_law_of_equal_psi

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hψ : ∀ θ : ℝ, 0 < θ → X.ψ θ = Y.ψ θ)
    (E : Set (ℝ≥0 → ℝ)) (hE : MeasurableSet E) :
    P₁ {ω : Ω₁ | (fun t : ℝ≥0 => X.X t ω) ∈ E} =
    P₂ {ω : Ω₂ | (fun t : ℝ≥0 => Y.X t ω) ∈ E} := by
  have hX : Measurable (fun ω : Ω₁ => fun t : ℝ≥0 => X.X t ω) :=
    measurable_pi_iff.mpr (fun t => X.adapted.measurable)
  have hY : Measurable (fun ω : Ω₂ => fun t : ℝ≥0 => Y.X t ω) :=
    measurable_pi_iff.mpr (fun t => Y.adapted.measurable)
  have hLaw := cross_levy_whole_path_law_of_equal_psi X Y hψ
  calc
    P₁ {ω : Ω₁ | (fun t : ℝ≥0 => X.X t ω) ∈ E} =
        (P₁.map (fun ω : Ω₁ => fun t : ℝ≥0 => X.X t ω)) E := by
          rw [Measure.map_apply hX hE]
          rfl
    _ = (P₂.map (fun ω : Ω₂ => fun t : ℝ≥0 => Y.X t ω)) E := by rw [hLaw]
    _ = P₂ {ω : Ω₂ | (fun t : ℝ≥0 => Y.X t ω) ∈ E} := by
          rw [Measure.map_apply hY hE]
          rfl