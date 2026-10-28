-- Prove2me | solution 1 for AvramDividend.Classical.cross_levy_zeroBasedGrid_law_of_marginals
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T14:45:49.33556+00:00
-- url     : https://prove2.me/submissions/8960d07e-5f12-4a71-a9c9-2783f994cb65

import Theorems.Thm_AvramDividend_Classical_cross_levy_finite_increment_vector_law_of_marginals
import Theorems.Thm_AvramDividend_Classical_cross_levy_incrementVector_law_implies_zeroBasedGrid_law
import Mathlib.MeasureTheory.MeasurableSpace.Defs

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
    (hMarginal : ∀ u : ℝ≥0, Measure.map (X.X u) P₁ = Measure.map (Y.X u) P₂)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (ht0 : t 0 = 0) (n : ℕ) :
    Measure.map (fun ω : Ω₁ => fun i : Fin n => X.X (t (i.val + 1)) ω) P₁ =
    Measure.map (fun ω : Ω₂ => fun i : Fin n => Y.X (t (i.val + 1)) ω) P₂ := by
  apply cross_levy_incrementVector_law_implies_zeroBasedGrid_law X Y t ht0 n
  exact cross_levy_finite_increment_vector_law_of_marginals
    X Y hMarginal t ht n
