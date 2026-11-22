-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsv_original_allnu_gaussian_stopped_grid_L2_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T12:50:47.087877+00:00
-- url     : https://prove2.me/submissions/beeb7143-1e53-4d3a-97ea-b6a5858cd3ef

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_allnu_Xminusjump_gaussian_martingale_and_sigma_square
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_zero_jump_process_fixed_time_square_moment_20261113
import Theorems.Thm_AvramDividend_Classical_avram_lsv_finite_grid_stopping_square_le

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
noncomputable section

/- Uses the actual original-process decomposition, existing Proved martingale
  and zero-jump Gaussian moment results, and the Lean-LSV countable-grid
  stopping contraction (CC BY 4.0, commit a5f604de2e1ae431de4cbecde23e5694a12ba719).
  No extra Brownian driver or martingale representation is assumed. -/

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
    MemLp (stoppedValue M τ) 2 P ∧
      (∫ ω, (stoppedValue M τ ω)^2 ∂P) ≤ (T : ℝ) * X.σ ^ 2 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let M : ℝ≥0 → Ω → ℝ := fun t ω =>
    X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
  change MemLp (stoppedValue M τ) 2 P ∧
    (∫ ω, (stoppedValue M τ ω)^2 ∂P) ≤ (T : ℝ) * X.σ ^ 2
  have hM : Martingale M 𝓕.rightCont P :=
    (avram_wave7_05_turn7_original_allnu_Xminusjump_gaussian_martingale_and_sigma_square
      X Y hYν hYσ Jsmall Jlarge hSourceDecomp).1
  have hEq : (fun ω => (M T ω)^2) =
      (fun ω => (Y.X T ω - (T : ℝ) * Y.c)^2) := by
    funext ω
    dsimp [M]
    rw [hSourceDecomp T ω]
    ring
  have hYM :=
    avram_a21_original_zero_jump_process_fixed_time_square_moment_20261113
      Y hYν T
  have hMom : Integrable (fun ω => (M T ω)^2) P ∧
      (∫ ω, (M T ω)^2 ∂P) = (T : ℝ) * X.σ ^ 2 := by
    rw [hEq]
    exact ⟨hYM.1, by simpa only [hYσ] using hYM.2⟩
  have hMPath : M T = (fun ω => Y.X T ω - (T : ℝ) * Y.c) := by
    funext ω
    dsimp [M]
    rw [hSourceDecomp T ω]
    ring
  have hMMeas : Measurable (M T) := by
    rw [hMPath]
    exact ((Y.adapted T).mono (𝓕.le T) le_rfl).sub_const _
  have hM2 : MemLp (M T) 2 P :=
    (memLp_two_iff_integrable_sq (μ := P)
      hMMeas.aestronglyMeasurable).2 hMom.1
  have hStop :=
    avram_lsv_finite_grid_stopping_square_le P 𝓕.rightCont
      M hM T hM2 τ hτ hτle hτcount
  exact ⟨hStop.1, hStop.2.trans_eq hMom.2⟩

