-- Prove2me | solution 1 for AvramDividend.Classical.cross_levy_whole_path_law_of_equal_psi
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T18:00:49.685251+00:00
-- url     : https://prove2.me/submissions/8fe08c0e-33d2-4c53-bd18-da8d8e78e55b

import Theorems.Thm_AvramDividend_Classical_cross_levy_whole_path_law_of_equal_marginals
import Theorems.Thm_AvramDividend_Classical_cross_levy_marginal_laws_of_equal_psi
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-!
All positive Laplace-exponent values uniquely determine the entire law
of a spectrally negative Lévy path, independent of its probability space.
-/
theorem solution
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hψ : ∀ θ : ℝ, 0 < θ → X.ψ θ = Y.ψ θ) :
    Measure.map (fun ω : Ω₁ => fun u : ℝ≥0 => X.X u ω) P₁ =
    Measure.map (fun ω : Ω₂ => fun u : ℝ≥0 => Y.X u ω) P₂ := by
  apply cross_levy_whole_path_law_of_equal_marginals X Y
  exact cross_levy_marginal_laws_of_equal_psi X Y hψ
