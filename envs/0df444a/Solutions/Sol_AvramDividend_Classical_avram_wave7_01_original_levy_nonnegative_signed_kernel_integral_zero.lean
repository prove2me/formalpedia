-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_original_levy_nonnegative_signed_kernel_integral_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T15:07:06.373206+00:00
-- url     : https://prove2.me/submissions/53239eec-c1c3-4bd1-bf1d-14387f82289b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (K : ℝ → ℝ) :
    (∫ y in Ici (0 : ℝ), K y ∂X.ν) = 0 := by
  have hRestrict : X.ν.restrict (Ici (0 : ℝ)) = 0 :=
    Measure.restrict_eq_zero.mpr X.ν_Ici
  change (∫ y, K y ∂(X.ν.restrict (Ici (0 : ℝ)))) = 0
  rw [hRestrict]
  exact integral_zero_measure K
