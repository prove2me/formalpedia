-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_sigma_zero_gaussian_residual_limit_ae_zero_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:42:28.541575+00:00
-- url     : https://prove2.me/submissions/5a826e4e-7c45-4b5d-915d-4a1414dcfc39

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_a21_finite_negative_activity_sigma_zero_implies_bounded_variation_20261113
import Theorems.Thm_AvramDividend_Classical_avram_ja18e_original_smallband_locally_uniform_cadlag_limit
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_finite_activity_BV_zero_cutoff_eq_full_compensated_negative_marks_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_gaussian_limit_eq_zero_residual_sub_full_compensated_smallmarks_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- A sigma-zero finite-negative-activity original Gaussian residual limit is zero a.e. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω)))
    (hSigma : X.σ = 0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, R t ω = 0 := by
  have hBV :=
    avram_a21_finite_negative_activity_sigma_zero_implies_bounded_variation_20261113
      X hFinite hSigma
  obtain ⟨Jsmall, hJsource, _, _⟩ :=
    avram_ja18e_original_smallband_locally_uniform_cadlag_limit
      X hX hFinite
  have hJdecomp :=
    avram_a21_original_finite_activity_BV_zero_cutoff_eq_full_compensated_negative_marks_20261113
      X hX hFinite hBV Jsmall hJsource
  have hRdecomp :=
    avram_a21_original_gaussian_limit_eq_zero_residual_sub_full_compensated_smallmarks_20261113
      X Jsmall R hJsource hR
  filter_upwards [hJdecomp, hRdecomp] with ω hJω hRω
  intro t
  rw [hRω t, hJω t, sub_self]
