-- Prove2me | solution 1 for AvramDividend.Classical.avram_jb20_original_physical_random_clock_increment_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T15:56:46.349587+00:00
-- url     : https://prove2.me/submissions/0d95f70f-7c78-482d-bba5-f3c41f279573

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_jb19_original_gaussian_residual_totalise_source_path
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Exact original physical increment decomposition between any two
random clocks, including source-exact Gaussian residual differences. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (nhds (Jsmall t ω))) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ t ω, X.X t ω =
        (t : ℝ) * X.c + M t ω + Jsmall t ω +
          avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, M t ω = R t ω) ∧
      (∀ α β : Ω → ℝ≥0, ∀ ω,
        X.X (β ω) ω - X.X (α ω) ω =
          ((β ω : ℝ) - (α ω : ℝ)) * X.c +
          (M (β ω) ω - M (α ω) ω) +
          (Jsmall (β ω) ω - Jsmall (α ω) ω) +
          (avram_p4_h_gaussian_intrinsic_large_jump_sum X (β ω) ω -
            avram_p4_h_gaussian_intrinsic_large_jump_sum X (α ω) ω)) ∧
      (∀ α β : Ω → ℝ≥0,
        (fun ω => M (β ω) ω - M (α ω) ω) =ᵐ[P]
          (fun ω => R (β ω) ω - R (α ω) ω)) := by
  classical
  obtain ⟨M, hpath, hMeq⟩ :=
    avram_jb19_original_gaussian_residual_totalise_source_path
      X R Jsmall hRsource hJsource
  refine ⟨M, hpath, hMeq, ?_, ?_⟩
  · intro α β ω
    have ht := hpath (β ω) ω
    have hs := hpath (α ω) ω
    rw [ht, hs]
    ring
  · intro α β
    filter_upwards [hMeq] with ω hω
    change M (β ω) ω - M (α ω) ω =
      R (β ω) ω - R (α ω) ω
    rw [hω (β ω), hω (α ω)]
