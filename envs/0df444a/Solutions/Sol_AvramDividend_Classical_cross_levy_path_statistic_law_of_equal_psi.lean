-- Prove2me | solution 1 for AvramDividend.Classical.cross_levy_path_statistic_law_of_equal_psi
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T20:47:19.800569+00:00
-- url     : https://prove2.me/submissions/e1bb5356-c619-4882-80af-8b13383bcd29

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Theorems.Thm_AvramDividend_Classical_cross_levy_whole_path_law_of_equal_psi

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {Ω₁ Ω₂ α : Type*}
    [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    [MeasurableSpace α]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hψ : ∀ θ : ℝ, 0 < θ → X.ψ θ = Y.ψ θ)
    (stat : (ℝ≥0 → ℝ) → α) (hstat : Measurable stat) :
    P₁.map (fun ω : Ω₁ => stat (fun t : ℝ≥0 => X.X t ω)) =
    P₂.map (fun ω : Ω₂ => stat (fun t : ℝ≥0 => Y.X t ω)) := by
  have hX : Measurable (fun ω : Ω₁ => fun t : ℝ≥0 => X.X t ω) :=
    measurable_pi_iff.mpr (fun t => X.adapted.measurable)
  have hY : Measurable (fun ω : Ω₂ => fun t : ℝ≥0 => Y.X t ω) :=
    measurable_pi_iff.mpr (fun t => Y.adapted.measurable)
  have hLaw := cross_levy_whole_path_law_of_equal_psi X Y hψ
  calc
    P₁.map (fun ω : Ω₁ => stat (fun t : ℝ≥0 => X.X t ω)) =
      (P₁.map (fun ω : Ω₁ => fun t : ℝ≥0 => X.X t ω)).map stat := by
        rw [Measure.map_map hstat hX]
        rfl
    _ = (P₂.map (fun ω : Ω₂ => fun t : ℝ≥0 => Y.X t ω)).map stat := by
        rw [hLaw]
    _ = P₂.map (fun ω : Ω₂ => stat (fun t : ℝ≥0 => Y.X t ω)) := by
        rw [Measure.map_map hstat hY]
        rfl