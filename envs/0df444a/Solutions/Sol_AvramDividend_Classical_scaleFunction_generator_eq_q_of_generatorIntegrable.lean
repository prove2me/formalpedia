-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generator_eq_q_of_generatorIntegrable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T07:06:11.14697+00:00
-- url     : https://prove2.me/submissions/ac2d0d9d-6fdc-4f09-9045-81736de73ac4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_of_local_regularity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_two_of_gaussian
import Theorems.Thm_AvramDividend_Classical_levyMeasure_absolutelyContinuous_of_standing_boundedVariation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_absolutely_continuous_levy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 W (Ioo 0 a))
    (hint : ∀ x ∈ Ioo 0 a, X.GeneratorIntegrable W x) :
    ∀ x ∈ Ioo 0 a,
      X.generator W x - q * W x = 0 := by
  have hsubset : Ioo (0 : ℝ) a ⊆ Ioi 0 := by
    intro x hx
    exact hx.1
  have hbvC1 (hbv : X.BoundedVariation) :
      ContDiffOn ℝ 1 W (Ioo 0 a) := by
    have hac : X.ν ≪ volume :=
      levyMeasure_absolutelyContinuous_of_standing_boundedVariation X hX hbv
    have hglobal : ContDiffOn ℝ 1 W (Ioi 0) :=
      scaleFunction_contDiff_one_of_absolutely_continuous_levy
        X hX q hq W hW hac
    exact hglobal.mono hsubset
  have hreg :
      (X.BoundedVariation ∧ ContDiffOn ℝ 1 W (Ioo 0 a)) ∨
      (¬ X.BoundedVariation ∧ ContDiffOn ℝ 2 W (Ioo 0 a)) := by
    by_cases hbv : X.BoundedVariation
    · exact Or.inl ⟨hbv, hbvC1 hbv⟩
    · right
      refine ⟨hbv, ?_⟩
      rcases h_smooth with hσ | hs
      · have hglobal : ContDiffOn ℝ 2 W (Ioi 0) :=
          scaleFunction_contDiff_two_of_gaussian X hX q hq W hW hσ
        exact hglobal.mono hsubset
      · rcases hs with hbv' | hC2
        · exact (hbv hbv').elim
        · exact hC2
  exact scaleFunction_generator_eq_q_of_local_regularity
    X hX q hq W hW a ha hint hreg
