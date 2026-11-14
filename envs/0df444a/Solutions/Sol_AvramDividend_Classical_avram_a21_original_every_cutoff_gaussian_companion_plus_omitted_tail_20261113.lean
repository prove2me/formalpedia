-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_every_cutoff_gaussian_companion_plus_omitted_tail_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:55:20.845638+00:00
-- url     : https://prove2.me/submissions/4aa27286-bd98-42e5-a636-4b61af75529b

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_residual_eq_zero_residual_sub_retained_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Physical finite-cutoff residual is Gaussian plus the OMITTED negative mark tail. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hDecomp : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω =
        (Y.X t ω - (t : ℝ) * Y.c) + Jsmall t ω) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ t : ℝ≥0,
      avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω =
        (Y.X t ω - (t : ℝ) * Y.c) +
          (Jsmall t ω -
            avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) := by
  filter_upwards [hDecomp] with ω hω
  intro n t
  have hSplit :=
    avram_a21_original_residual_eq_zero_residual_sub_retained_20261113
      X n t ω
  rw [hω t] at hSplit
  linarith
