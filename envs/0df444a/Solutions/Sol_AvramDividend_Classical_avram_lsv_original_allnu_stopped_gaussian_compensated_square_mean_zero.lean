-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsv_original_allnu_stopped_gaussian_compensated_square_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T12:58:06.060018+00:00
-- url     : https://prove2.me/submissions/a5fa62be-6ee4-43be-847c-b202fccff507

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_allnu_Xminusjump_gaussian_martingale_and_sigma_square
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_zero_jump_process_fixed_time_square_moment_20261113
import Theorems.Thm_AvramDividend_Classical_avram_lsv_finite_grid_stopped_martingale_expectation

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
noncomputable section

/- Actual original X-minus-physical-jumps stopped Gaussian compensated square.
   Uses proved same-space Gaussian decomposition, square martingale and the
   Lean-LSV bounded countable-range optional expectation (CC BY 4.0,
   original upstream commit a5f604de2e1ae431de4cbecde23e5694a12ba719). -/

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
    let Q : ℝ≥0 → Ω → ℝ := fun t ω =>
      (M t ω)^2 - (t : ℝ) * X.σ^2
    Integrable (stoppedValue Q τ) P ∧
      (∫ ω, stoppedValue Q τ ω ∂P) = 0 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let M : ℝ≥0 → Ω → ℝ := fun t ω =>
    X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
  let Q : ℝ≥0 → Ω → ℝ := fun t ω =>
    (M t ω)^2 - (t : ℝ) * X.σ^2
  change Integrable (stoppedValue Q τ) P ∧
    (∫ ω, stoppedValue Q τ ω ∂P) = 0
  have hQ : Martingale Q 𝓕.rightCont P :=
    (avram_wave7_05_turn7_original_allnu_Xminusjump_gaussian_martingale_and_sigma_square
      X Y hYν hYσ Jsmall Jlarge hSourceDecomp).2
  obtain ⟨hi, he⟩ :=
    avram_lsv_finite_grid_stopped_martingale_expectation
      P 𝓕.rightCont Q hQ T τ hτ hτle hτcount
  refine ⟨hi, he.trans ?_⟩
  have hMPath : M T = (fun ω => Y.X T ω - (T : ℝ) * Y.c) := by
    funext ω
    dsimp [M]
    rw [hSourceDecomp T ω]
    ring
  have hYMom :=
    avram_a21_original_zero_jump_process_fixed_time_square_moment_20261113
      Y hYν T
  have hm : Integrable (fun ω => (M T ω)^2) P ∧
      (∫ ω, (M T ω)^2 ∂P) = (T : ℝ) * X.σ^2 := by
    rw [hMPath]
    exact ⟨hYMom.1, by simpa only [hYσ] using hYMom.2⟩
  change (∫ ω, (M T ω)^2 - (T : ℝ) * X.σ^2 ∂P) = 0
  rw [integral_sub hm.1 (integrable_const _), hm.2]
  simp

