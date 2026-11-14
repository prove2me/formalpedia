-- Prove2me | solution 1 for AvramDividend.Classical.avram_a22_original_zero_nu_intrinsic_gaussian_limit_sameX_companion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T20:57:22.516195+00:00
-- url     : https://prove2.me/submissions/7ef869ab-5e5c-46e7-b934-1fb9667b87d1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_zero_nu_every_positive_time_no_actual_jump_ae
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_nojump_zero_nu_smallband_identically_zero
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_truly_jumpless_large_mark_sum_identically_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- With no original Lévy marks the genuine Gaussian residual is simply the original centred Lévy process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNu : X.ν = 0)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω))) :
    ∃ Y : SpectrallyNegativeLevy P 𝓕,
      Y.ν = 0 ∧ Y.σ = X.σ ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        R t ω = Y.X t ω - (t : ℝ) * Y.c) := by
  refine ⟨X, hNu, rfl, ?_⟩
  have hNoJump :=
    avram_a22_original_zero_nu_every_positive_time_no_actual_jump_ae X hNu
  filter_upwards [hNoJump, hR] with ω hJumpω hRω
  intro t
  have hLarge :=
    avram_a22_original_truly_jumpless_large_mark_sum_identically_zero X ω hJumpω t
  have hResidual (n : ℕ) :
      avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω =
        X.X t ω - (t : ℝ) * X.c := by
    have hSmall :=
      avram_a22_original_nojump_zero_nu_smallband_identically_zero
        X hNu ω hJumpω n t
    unfold avram_p4_h_gaussian_intrinsic_truncated_residual
    rw [hSmall, hLarge]
    ring
  have hConst :
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (X.X t ω - (t : ℝ) * X.c)) := by
    simpa only [hResidual] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => X.X t ω - (t : ℝ) * X.c)
          atTop (𝓝 (X.X t ω - (t : ℝ) * X.c)))
  exact tendsto_nhds_unique (hRω t) hConst
