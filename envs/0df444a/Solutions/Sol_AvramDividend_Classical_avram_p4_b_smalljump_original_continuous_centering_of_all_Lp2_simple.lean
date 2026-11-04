-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_continuous_centering_of_all_Lp2_simple
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:28:42.643397+00:00
-- url     : https://prove2.me/submissions/1743eb00-3ab4-4c3c-9eba-389fc696aaca

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_continuous_centering_of_dense_simple
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_mark_Lp2_simple_dense
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original-source zero expectation of compensated integration extends
from all L2 simple inputs to arbitrary predictable L2 inputs once the
source integral and expectation linear maps are genuinely constructed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      ∀ (I : Lp ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))) →L[ℝ] Lp ℝ (2 : ℝ≥0∞) P)
        (J : Lp ℝ (2 : ℝ≥0∞) P →L[ℝ] ℝ)
        (hSimpleZero : ∀ v : ↥(Lp.simpleFunc ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0)))),
          J (I (v : Lp ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))))) = 0),
      ∀ v, J (I v) = 0) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  intro I J hSimpleZero
  have hDense : Dense (↑(Lp.simpleFunc ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0)))) :
      Set (Lp ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))))) :=
    Lp.simpleFunc.dense (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  apply avram_p4_b_smalljump_original_continuous_centering_of_dense_simple
    X μ I J _ hDense
  intro v hv
  exact hSimpleZero ⟨v, hv⟩
