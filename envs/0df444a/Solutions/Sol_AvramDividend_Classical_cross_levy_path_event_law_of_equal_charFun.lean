-- Prove2me | solution 1 for AvramDividend.Classical.cross_levy_path_event_law_of_equal_charFun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:53:10.082716+00:00
-- url     : https://prove2.me/submissions/c507e55d-a07b-4700-81e4-4a92c4ddfad2

import Mathlib.MeasureTheory.Measure.Map
import Theorems.Thm_AvramDividend_Classical_cross_levy_whole_path_law_of_equal_charFun

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/--
Matching characteristic functions of all Lévy time-marginals transfer
every measurable whole-path event between independent sample spaces.
-/
theorem solution
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hchar : ∀ t : ℝ≥0, ∀ ξ : ℝ,
      charFun (Measure.map (X.X t) P₁) ξ =
      charFun (Measure.map (Y.X t) P₂) ξ)
    (E : Set (ℝ≥0 → ℝ)) (hE : MeasurableSet E) :
    P₁ {ω : Ω₁ | (fun t : ℝ≥0 => X.X t ω) ∈ E} =
    P₂ {ω : Ω₂ | (fun t : ℝ≥0 => Y.X t ω) ∈ E} := by
  have hPX : Measurable (fun ω : Ω₁ => fun t : ℝ≥0 => X.X t ω) :=
    measurable_pi_lambda _ fun t => X.adapted.measurable
  have hPY : Measurable (fun ω : Ω₂ => fun t : ℝ≥0 => Y.X t ω) :=
    measurable_pi_lambda _ fun t => Y.adapted.measurable
  have hLaw := cross_levy_whole_path_law_of_equal_charFun X Y hchar
  calc
    P₁ {ω : Ω₁ | (fun t : ℝ≥0 => X.X t ω) ∈ E} =
        (Measure.map (fun ω : Ω₁ => fun t : ℝ≥0 => X.X t ω) P₁) E :=
          (Measure.map_apply hPX hE).symm
    _ = (Measure.map (fun ω : Ω₂ => fun t : ℝ≥0 => Y.X t ω) P₂) E :=
      congrArg (fun μ : Measure (ℝ≥0 → ℝ) => μ E) hLaw
    _ = P₂ {ω : Ω₂ | (fun t : ℝ≥0 => Y.X t ω) ∈ E} :=
      Measure.map_apply hPY hE
