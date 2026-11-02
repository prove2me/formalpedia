-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generator_eq_q_of_stoppedScaleIdentity_corrected
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:43:04.540629+00:00
-- url     : https://prove2.me/submissions/16919f91-70ab-403c-adc6-5516101f873c

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
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
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 W (Ioo 0 a))
    (hint : ∀ x ∈ Ioo 0 a, X.GeneratorIntegrable W x)
    (hstop : ∀ b y : ℝ, 0 < b → 0 ≤ y → y ≤ b →
      twoSidedExitExpectationCorrected X q b y *
          ENNReal.ofReal (W b) =
        ENNReal.ofReal (W y)) :
    ∀ x ∈ Ioo 0 a,
      X.generator W x - q * W x = 0 := by
  exact scaleFunction_generator_eq_q_of_generatorIntegrable
    X hX q hq W hW a ha h_smooth hint
