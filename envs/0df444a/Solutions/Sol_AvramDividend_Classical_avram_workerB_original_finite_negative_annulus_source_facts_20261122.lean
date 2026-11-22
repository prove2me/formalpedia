-- Prove2me | solution 1 for AvramDividend.Classical.avram_workerB_original_finite_negative_annulus_source_facts_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T10:10:54.554691+00:00
-- url     : https://prove2.me/submissions/8d0045d3-4264-4f6e-b785-67ab6a5d61bc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_negative_jump_truncation_measure_finite
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n m : ℕ) :
    let B : Set ℝ :=
      Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    MeasurableSet B ∧ B ⊆ Iio (0 : ℝ) ∧ X.ν B < ⊤ := by
  classical
  let B : Set ℝ :=
    Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
  change MeasurableSet B ∧ B ⊆ Iio (0 : ℝ) ∧ X.ν B < ⊤
  refine ⟨measurableSet_Ioc, ?_, ?_⟩
  · intro z hz
    have hε : 0 < 1 / ((m : ℝ) + 1) := by positivity
    exact lt_of_le_of_lt hz.2 (neg_neg_of_pos hε)
  · have hε : 0 < 1 / ((m : ℝ) + 1) := by positivity
    have hSubset :
        B ⊆ Iic (-(1 / ((m : ℝ) + 1))) := by
      intro z hz
      exact hz.2
    exact lt_of_le_of_lt (measure_mono hSubset)
      (negative_jump_truncation_measure_finite X.ν
        X.ν_integrable (1 / ((m : ℝ) + 1)) hε)
