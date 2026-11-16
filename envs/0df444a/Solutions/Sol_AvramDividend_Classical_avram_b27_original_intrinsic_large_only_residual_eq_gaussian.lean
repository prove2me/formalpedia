-- Prove2me | solution 1 for AvramDividend.Classical.avram_b27_original_intrinsic_large_only_residual_eq_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:44:09.533209+00:00
-- url     : https://prove2.me/submissions/a3fcccb7-5082-447d-b80a-80de30300cf2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_b27_original_no_small_band_marks_compensator_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (B N : ℝ≥0 → ℝ)
    (hc : X.c = 0)
    (hν : X.ν (Ioc (-1 : ℝ) 0) = 0)
    (hPath : ∀ t : ℝ≥0, X.X t ω = B t - 2 * N t)
    (hLargeSum : ∀ t : ℝ≥0,
      avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω = -2 * N t)
    (hJumps : ∀ u : ℝ≥0, 0 < u →
      (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 ∨
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -1)) :
    ∀ (k : ℕ) (t : ℝ≥0),
      avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω = B t := by
  intro k t
  have hSmall :
      avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω = 0 :=
    avram_b27_original_no_small_band_marks_compensator_zero
      X hν ω hJumps k t
  change X.X t ω - (t : ℝ) * X.c -
    avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω -
    avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω = B t
  rw [hPath t, hc, hSmall, hLargeSum t]
  ring
