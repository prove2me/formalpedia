-- Prove2me | solution 2 for AvramDividend.Classical.scaleFunction_generator_eq_q_of_local_regularity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:41:25.132465+00:00
-- url     : https://prove2.me/submissions/1d6484e6-b3e8-4570-9424-387fe6a89856

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_of_generatorIntegrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hint : ∀ x ∈ Ioo 0 a, X.GeneratorIntegrable W x)
    (hreg :
      (X.BoundedVariation ∧ ContDiffOn ℝ 1 W (Ioo 0 a)) ∨
      (¬ X.BoundedVariation ∧ ContDiffOn ℝ 2 W (Ioo 0 a))) :
    ∀ x ∈ Ioo 0 a,
      X.generator W x - q * W x = 0 := by
  have h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 W (Ioo 0 a) := by
    rcases hreg with ⟨hbv, _⟩ | ⟨_, hC2⟩
    · exact Or.inr (Or.inl hbv)
    · exact Or.inr (Or.inr hC2)
  exact scaleFunction_generator_eq_q_of_generatorIntegrable
    X hX q hq W hW a ha h_smooth hint
