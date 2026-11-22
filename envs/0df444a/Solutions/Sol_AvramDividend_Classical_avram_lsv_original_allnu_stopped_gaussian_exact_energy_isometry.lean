-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsv_original_allnu_stopped_gaussian_exact_energy_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T13:08:19.421794+00:00
-- url     : https://prove2.me/submissions/32e326f2-678b-4409-95aa-4edf4a9ee525

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_allnu_Xminusjump_gaussian_martingale_and_sigma_square
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_zero_jump_process_fixed_time_square_moment_20261113
import Theorems.Thm_AvramDividend_Classical_avram_lsv_finite_grid_stopped_quadratic_energy_isometry

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
noncomputable section

/- Actual original spectrally negative Levy X, physical small and large jump
   channels, with explicitly given same-space Y Gaussian driver. Port of
   lean-lsv exact stopped quadratic energy identity at bounded countable
   stopping clocks. Upstream CC BY 4.0, commit a5f604d. -/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c +
        (Y.X t ω - (t : ℝ) * Y.c) + Jsmall t ω + Jlarge t ω)
    (T : ℝ≥0) (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont τ)
    (hτle : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hτcount : (Set.range τ).Countable) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    Integrable (fun ω => ((τ ω).untopA : ℝ) * X.σ^2) P ∧
      (∫ ω, (stoppedValue M τ ω)^2 ∂P) =
        ∫ ω, ((τ ω).untopA : ℝ) * X.σ^2 ∂P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let M : ℝ≥0 → Ω → ℝ := fun t ω =>
    X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
  let A : ℝ≥0 → Ω → ℝ := fun t _ => (t : ℝ) * X.σ^2
  change Integrable (fun ω => A (τ ω).untopA ω) P ∧
    (∫ ω, (stoppedValue M τ ω)^2 ∂P) =
      ∫ ω, A (τ ω).untopA ω ∂P
  obtain ⟨hM, hQ⟩ :=
    avram_wave7_05_turn7_original_allnu_Xminusjump_gaussian_martingale_and_sigma_square
      X Y hYν hYσ Jsmall Jlarge hSourceDecomp
  have hMPath : M T = (fun ω => Y.X T ω - (T : ℝ) * Y.c) := by
    funext ω
    dsimp [M]
    rw [hSourceDecomp T ω]
    ring
  have hYMom :=
    avram_a21_original_zero_jump_process_fixed_time_square_moment_20261113
      Y hYν T
  have hMom : Integrable (fun ω => (M T ω)^2) P ∧
      (∫ ω, (M T ω)^2 ∂P) = (T : ℝ) * X.σ^2 := by
    rw [hMPath]
    exact ⟨hYMom.1, by simpa only [hYσ] using hYMom.2⟩
  have hMMeas : Measurable (M T) := by
    rw [hMPath]
    exact ((Y.adapted T).mono (𝓕.le T) le_rfl).sub_const _
  have hM2 : MemLp (M T) 2 P :=
    (memLp_two_iff_integrable_sq (μ := P)
      hMMeas.aestronglyMeasurable).2 hMom.1
  have hQTzero : (∫ ω, (M T ω)^2 - A T ω ∂P) = 0 := by
    change (∫ ω, (M T ω)^2 - (T : ℝ) * X.σ^2 ∂P) = 0
    rw [integral_sub hMom.1 (integrable_const _), hMom.2]
    simp
  exact avram_lsv_finite_grid_stopped_quadratic_energy_isometry
    P 𝓕.rightCont M A hM hQ T hM2 hQTzero τ hτ hτle hτcount

