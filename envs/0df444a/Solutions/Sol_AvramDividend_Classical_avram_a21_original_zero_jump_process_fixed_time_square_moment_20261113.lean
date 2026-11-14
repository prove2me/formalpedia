-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_zero_jump_process_fixed_time_square_moment_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:56:18.352203+00:00
-- url     : https://prove2.me/submissions/9b098fb8-523d-4086-934c-786c31183353

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_variance
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_exact_variance
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Pure Gaussian Levy source has exact drift-centred second moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕) (hν : Y.ν = 0)
    (t : ℝ≥0) :
    Integrable (fun ω => (Y.X t ω - (t : ℝ) * Y.c) ^ 2) P ∧
      (∫ ω, (Y.X t ω - (t : ℝ) * Y.c) ^ 2 ∂P) =
        (t : ℝ) * Y.σ ^ 2 := by
  have hI :=
    avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_variance
      Y hν 0 t (show (0 : ℝ≥0) ≤ t from zero_le)
  have hInt : Integrable (fun ω => (Y.X t ω - (t : ℝ) * Y.c) ^ 2) P := by
    simpa [Y.X_zero] using hI.1
  let τ : Ω → ℝ≥0 := fun _ => 0
  have hτ : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)) := by
    simpa [τ] using (isStoppingTime_const (𝓕.rightCont) (0 : ℝ≥0))
  have hBound : ∀ ω, τ ω ≤ (0 : ℝ≥0) := by
    intro ω
    simp [τ]
  have hVar :=
    avram_wave6_03_original_rightCont_stopped_gaussian_exact_variance
      Y hν τ hτ 0 hBound t
  have hEq : (∫ ω, (Y.X t ω - (t : ℝ) * Y.c) ^ 2 ∂P) =
      (t : ℝ) * Y.σ ^ 2 := by
    simpa [τ, Y.X_zero] using hVar
  exact ⟨hInt, hEq⟩
