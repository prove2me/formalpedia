-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_continuous_isometry_of_all_Lp2_simple
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:27:40.546895+00:00
-- url     : https://prove2.me/submissions/3d0767b0-2522-47af-8f7c-e521a6b9da16

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_continuous_isometry_of_dense_simple
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_mark_Lp2_simple_dense
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Once true original-source compensated integration is a continuous linear
map and its norm identity holds for every source Lp2 simple integrand, the
actual dense simple class gives the full L2 isometry automatically. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      ∀ (I : Lp ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))) →L[ℝ] Lp ℝ (2 : ℝ≥0∞) P)
        (hSimpleIso : ∀ v : ↥(Lp.simpleFunc ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0)))),
          ‖I (v : Lp ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))))‖ =
          ‖(v : Lp ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))))‖),
      ∀ v, ‖I v‖ = ‖v‖) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  intro I hSimpleIso
  have hDense : Dense (↑(Lp.simpleFunc ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0)))) :
      Set (Lp ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))))) :=
    Lp.simpleFunc.dense (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  apply avram_p4_b_smalljump_original_continuous_isometry_of_dense_simple
    X μ I _ hDense
  intro v hv
  exact hSimpleIso ⟨v, hv⟩
