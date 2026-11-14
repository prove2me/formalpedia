-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb22_original_zero_barrier_admissible_at_any_positive_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:13:09.886586+00:00
-- url     : https://prove2.me/submissions/6e8a8f09-1eaf-4f68-a89e-8169adc76fac

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_admissibleLe_nonnegative_barrier
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) :
    IsAdmissibleLe X 0 C (barrierStrategy X 0 0)  := by
  have hzero :=
    barrierStrategy_admissibleLe_nonnegative_barrier
      X 0 0 (le_refl 0) (le_refl 0)
  have hzeroCap : (ENNReal.ofReal (0 : ℝ)) ≤ C := by
    simpa using hC.le
  exact ⟨hzero.1, fun ω t ht => (hzero.2 ω t ht).trans hzeroCap⟩
