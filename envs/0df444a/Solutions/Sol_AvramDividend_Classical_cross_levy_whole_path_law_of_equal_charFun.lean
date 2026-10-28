-- Prove2me | solution 1 for AvramDividend.Classical.cross_levy_whole_path_law_of_equal_charFun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:37:52.983887+00:00
-- url     : https://prove2.me/submissions/dc6a842d-167f-4f90-b290-f8156f594f2b

import Theorems.Thm_AvramDividend_Classical_cross_levy_whole_path_law_of_equal_marginals
import Theorems.Thm_AvramDividend_Classical_cross_levy_marginal_laws_of_equal_charFun
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-!
The law of an entire Lévy path is determined by all one-time characteristic
functions, even when the processes live on different probability spaces.
-/
theorem solution
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hchar : ∀ t : ℝ≥0, ∀ ξ : ℝ,
      charFun (Measure.map (X.X t) P₁) ξ =
      charFun (Measure.map (Y.X t) P₂) ξ) :
    Measure.map (fun ω : Ω₁ => fun u : ℝ≥0 => X.X u ω) P₁ =
    Measure.map (fun ω : Ω₂ => fun u : ℝ≥0 => Y.X u ω) P₂ := by
  apply cross_levy_whole_path_law_of_equal_marginals X Y
  exact cross_levy_marginal_laws_of_equal_charFun X Y hchar
