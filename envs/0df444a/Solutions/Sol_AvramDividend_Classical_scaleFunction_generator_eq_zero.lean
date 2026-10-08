-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generator_eq_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T21:00:21.68328+00:00
-- url     : https://prove2.me/submissions/3ce8d32b-f039-466e-bf81-6937df25018a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_smooth
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_of_generatorIntegrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (a : ℝ) (ha : 0 < a)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ∀ x ∈ Ioo 0 a,
      X.GeneratorIntegrable W x ∧ X.generator W x - q * W x = 0 := by
  have hint :=
    scaleFunction_generatorIntegrable_of_smooth
      X hX q hq W hW a ha h_smooth
  have heq :=
    scaleFunction_generator_eq_q_of_generatorIntegrable
      X hX q hq W hW a ha h_smooth hint
  intro x hx
  exact ⟨hint x hx, heq x hx⟩
