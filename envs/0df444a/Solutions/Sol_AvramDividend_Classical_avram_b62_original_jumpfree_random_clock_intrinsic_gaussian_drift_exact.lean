-- Prove2me | solution 1 for AvramDividend.Classical.avram_b62_original_jumpfree_random_clock_intrinsic_gaussian_drift_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:45:56.723322+00:00
-- url     : https://prove2.me/submissions/375a9175-524e-40b2-98fc-877b00f7abc0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_jb20_original_physical_random_clock_increment_split
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Same original path random-clock jump-free Gaussian residual and finite-activity drift split. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
        atTop (𝓝 (R u ω)))
    (hJsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ => avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
        atTop (𝓝 (Jsmall u ω)))
    (s t : Ω → ℝ≥0) (d : ℝ)
    (hSmall : ∀ ω, Jsmall (t ω) ω - Jsmall (s ω) ω =
      d * ((t ω : ℝ) - (s ω : ℝ)))
    (hLarge : ∀ ω,
      avram_p4_h_gaussian_intrinsic_large_jump_sum X (t ω) ω =
      avram_p4_h_gaussian_intrinsic_large_jump_sum X (s ω) ω) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ ω,
        X.X (t ω) ω - X.X (s ω) ω -
          ((t ω : ℝ) - (s ω : ℝ)) * X.c =
        (M (t ω) ω - M (s ω) ω) +
          d * ((t ω : ℝ) - (s ω : ℝ))) ∧
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0, M u ω = R u ω) := by 
  obtain ⟨M, hPath, hMsource, hInc, hIncAE⟩ :=
    avram_jb20_original_physical_random_clock_increment_split
      X R Jsmall hRsource hJsource
  refine ⟨M, ?_, hMsource⟩
  intro ω
  have hh := hInc s t ω
  have hL :
      avram_p4_h_gaussian_intrinsic_large_jump_sum X (t ω) ω -
      avram_p4_h_gaussian_intrinsic_large_jump_sum X (s ω) ω = 0 := by
    rw [hLarge ω]
    ring
  rw [hSmall ω, hL] at hh
  linarith
