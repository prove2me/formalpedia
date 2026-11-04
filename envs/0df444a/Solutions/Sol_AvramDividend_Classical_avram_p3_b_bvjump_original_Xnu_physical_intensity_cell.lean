-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_Xnu_physical_intensity_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:32:38.785742+00:00
-- url     : https://prove2.me/submissions/6f843737-f997-4254-b9be-9c4cb658b34a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_predictable_marked_intensity_cell
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_levy_negative_restrict_eq_self
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_levy_intensity_sigmafinite_from_process_fields
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable;
      μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
    (s t : ℝ≥0) (A : Set Ω) (B : Set ℝ) :
    N ((Ioc s t ×ˢ A) ×ˢ B) =
      μ (Ioc s t ×ˢ A) * X.ν B := by
  letI : SigmaFinite X.ν :=
    avram_wave5_01_actual_source_levy_intensity_sigmafinite_from_process_fields X
  have hN' : N =
      (letI : MeasurableSpace (ℝ≥0 × Ω) :=
        𝓕.rightCont.predictable; μ.prod X.ν) := by
    rw [hN, avram_p3_b_bvjump_original_levy_negative_restrict_eq_self X]
  exact avram_p3_b_bvjump_original_predictable_marked_intensity_cell
    𝓕 μ X.ν N hN' s t A B
