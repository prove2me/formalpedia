-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja19_public_original_compensated_smallband_eq_finite_jump_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:47:51.614786+00:00
-- url     : https://prove2.me/submissions/4a0deaec-0da1-48b2-81bb-48bb0ff9b83e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja18j_public_original_compensated_finsum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Reuse the verified same-original-space finite-band sum identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) (T : ℝ≥0) (ω : Ω) :
    let j : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    ∃ F : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧ -1 < j u ∧
        j u ≤ -(1 / ((n : ℝ) + 1))) ∧
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω =
        (∑ u ∈ F, j u) -
          (T : ℝ) * (∫ z in Ioc (-1 : ℝ)
            (-(1 / ((n : ℝ) + 1))), z ∂X.ν) := by
  exact avram_ja18j_public_original_compensated_finsum X n T ω
