-- Prove2me | solution 1 for AvramDividend.Classical.cross_levy_marginal_laws_of_equal_charFun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:01:26.847713+00:00
-- url     : https://prove2.me/submissions/8894defa-495f-41a0-8063-c95bd805a34e

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω₁ Ω₂ : Type*}
    [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hchar : ∀ t : ℝ≥0, ∀ ξ : ℝ,
      charFun (Measure.map (X.X t) P₁) ξ =
      charFun (Measure.map (Y.X t) P₂) ξ) :
    ∀ t : ℝ≥0,
      Measure.map (X.X t) P₁ = Measure.map (Y.X t) P₂ := by
  letI : IsProbabilityMeasure P₁ := X.isProbability
  letI : IsProbabilityMeasure P₂ := Y.isProbability
  intro t
  have hmX : Measurable (X.X t) := X.adapted.measurable
  have hmY : Measurable (Y.X t) := Y.adapted.measurable
  haveI : IsProbabilityMeasure (Measure.map (X.X t) P₁) :=
    Measure.isProbabilityMeasure_map hmX.aemeasurable
  haveI : IsProbabilityMeasure (Measure.map (Y.X t) P₂) :=
    Measure.isProbabilityMeasure_map hmY.aemeasurable
  apply Measure.ext_of_charFun
  exact funext (hchar t)
