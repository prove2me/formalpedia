-- Prove2me | solution 1 for FeynmanKac.augmented_vector_ito_representation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T09:07:56.807914+00:00
-- url     : https://prove2.me/submissions/eea4e8e5-5ac0-4d10-aa1b-1c91220eb9c2

import Definitions.Def_FeynmanKac_BoundedDiffusionModel
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoProcessVersion
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

open MeasureTheory
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P) :
    ∃ (hm : ∀ (i : Fin 2) (k : Fin 1),
         Measurable (Function.uncurry fun ω s =>
           m.augmentedVolatility (m.augmentedPath s ω) k i))
      (hp : ∀ (i : Fin 2) (k : Fin 1),
         LevyStochCalc.Probability.ProgressivelyMeasurable m.filtration
           (fun ω s => m.augmentedVolatility (m.augmentedPath s ω) k i))
      (hq : ∀ (i : Fin 2) (k : Fin 1) (T : ℝ), 0 < T →
         ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
           (‖m.augmentedVolatility (m.augmentedPath s ω) k i‖₊ : ℝ≥0∞)^2
             ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤),
      LevyStochCalc.Brownian.Ito.IsVectorItoVersion
        m.brownian m.filtration m.brownianFiltration
        (fun i k ω s => m.augmentedVolatility (m.augmentedPath s ω) k i)
        hm hp hq
        (fun _ => m.initialCoordinates)
        (fun i ω s => m.augmentedDrift (m.augmentedPath s ω) i)
        m.augmentedPath := by
  exact m.isDiffusion
