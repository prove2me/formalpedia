-- Prove2me | solution 1 for AvramDividend.Classical.cross_levy_whole_path_law_of_equal_triplet
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T18:44:31.06761+00:00
-- url     : https://prove2.me/submissions/0935365b-cece-478d-b822-9343bde3b997

import Theorems.Thm_AvramDividend_Classical_cross_levy_whole_path_law_of_equal_psi
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/--
Lévy processes on unrelated sample spaces have identical full path laws
when their drift, Gaussian coefficient and Lévy jump measures coincide.
-/
theorem solution
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hc : X.c = Y.c) (hσ : X.σ = Y.σ) (hν : X.ν = Y.ν) :
    Measure.map (fun ω : Ω₁ => fun t : ℝ≥0 => X.X t ω) P₁ =
    Measure.map (fun ω : Ω₂ => fun t : ℝ≥0 => Y.X t ω) P₂ := by
  apply cross_levy_whole_path_law_of_equal_psi X Y
  intro θ hθ
  change laplaceExponent X.c X.σ X.ν θ =
    laplaceExponent Y.c Y.σ Y.ν θ
  rw [hc, hσ, hν]
