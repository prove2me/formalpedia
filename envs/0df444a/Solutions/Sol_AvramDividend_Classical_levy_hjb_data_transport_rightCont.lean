-- Prove2me | solution 1 for AvramDividend.Classical.levy_hjb_data_transport_rightCont
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T19:34:25.817361+00:00
-- url     : https://prove2.me/submissions/3743367b-7920-4852-8e12-8a1b88f7cb4b

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : SpectrallyNegativeLevy P 𝓕.rightCont)
    (hX : Y.X = X.X)
    (hc : Y.c = X.c) (hσ : Y.σ = X.σ)
    (hν : Y.ν = X.ν)
    (hstand : X.Standing) :
    Y.Standing ∧
      (∀ (f : ℝ → ℝ) (z : ℝ), Y.generator f z = X.generator f z) ∧
      (∀ (f : ℝ → ℝ) (z : ℝ),
        Y.GeneratorIntegrable f z ↔ X.GeneratorIntegrable f z) := by
  have hmono : Y.HasMonotonePaths ↔ X.HasMonotonePaths := by
    simp [SpectrallyNegativeLevy.HasMonotonePaths,
      SpectrallyNegativeLevy.BoundedVariation,
      SpectrallyNegativeLevy.drift, hc, hσ, hν]
  have hcond : Y.Condition33 ↔ X.Condition33 := by
    simp [SpectrallyNegativeLevy.Condition33, hσ, hν]
  refine ⟨⟨(fun hy => hstand.1 (hmono.mp hy)), ?_, hcond.mpr hstand.2.2⟩, ?_, ?_⟩
  · simpa only [hX] using hstand.2.1
  · intro f z
    simp [SpectrallyNegativeLevy.generator, hc, hσ, hν]
  · intro f z
    simp [SpectrallyNegativeLevy.GeneratorIntegrable, hν]
