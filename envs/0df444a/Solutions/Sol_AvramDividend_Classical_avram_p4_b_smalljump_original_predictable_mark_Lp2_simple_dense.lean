-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_predictable_mark_Lp2_simple_dense
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:16:13.156401+00:00
-- url     : https://prove2.me/submissions/67d772eb-f7b6-4d49-9569-4dc0ca991fb0

import Mathlib
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Square-integrable finite-valued simple functions are dense in the
actual original predictable time-space and small-negative Lévy mark L2.
This source-specific density does not supply jump-count covariance. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      DenseRange
        (Subtype.val :
          ↥(Lp.simpleFunc ℝ (2 : ℝ≥0∞)
            (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0)))) →
          Lp ℝ (2 : ℝ≥0∞)
            (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))))) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  exact Lp.simpleFunc.denseRange (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
