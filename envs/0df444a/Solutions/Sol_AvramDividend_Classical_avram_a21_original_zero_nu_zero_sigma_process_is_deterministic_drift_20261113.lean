-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_zero_nu_zero_sigma_process_is_deterministic_drift_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:03:30.429584+00:00
-- url     : https://prove2.me/submissions/8b4f3676-a6f4-4bb6-8704-48f55f8f4588

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_zero_jump_process_fixed_time_square_moment_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original zero-jump zero-sigma Levy process is drift at each fixed horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕)
    (hν : Y.ν = 0) (hσ : Y.σ = 0) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, Y.X t ω = (t : ℝ) * Y.c := by
  have hSq :=
    avram_a21_original_zero_jump_process_fixed_time_square_moment_20261113
      Y hν t
  have hInt : (∫ ω, (Y.X t ω - (t : ℝ) * Y.c) ^ 2 ∂P) = 0 := by
    simpa [hσ] using hSq.2
  have hNonneg : 0 ≤
      (fun ω : Ω => (Y.X t ω - (t : ℝ) * Y.c) ^ 2) := by
    intro ω
    exact sq_nonneg _
  have hZero :=
    (integral_eq_zero_iff_of_nonneg hNonneg hSq.1).1 hInt
  filter_upwards [hZero] with ω hω
  change (Y.X t ω - (t : ℝ) * Y.c) ^ 2 = 0 at hω
  nlinarith
