-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsv_original_zerojump_stopped_gaussian_exact_energy_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T13:06:33.966716+00:00
-- url     : https://prove2.me/submissions/a4c66d1b-63f6-4d29-b7fd-89b09c39a529

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_zerojump_centered_source_martingale
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_zerojump_centered_source_square_martingale
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_zero_jump_process_fixed_time_square_moment_20261113
import Theorems.Thm_AvramDividend_Classical_avram_lsv_finite_grid_stopped_quadratic_energy_isometry

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
noncomputable section

/-
Exact original-process stopped Gaussian isometry from the true quadratic
martingale and the stopped energy lemma adapted from dufeteller/lean-lsv,
LSV/LocalizedStoppingL2Convergence.lean and LocalizedOptionalExpectation.lean,
commit a5f604de2e1ae431de4cbecde23e5694a12ba719, CC BY 4.0.
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont τ)
    (hτle : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hτcount : (Set.range τ).Countable) :
    let M : ℝ≥0 → Ω → ℝ := fun s ω => X.X s ω - (s : ℝ) * X.c
    Integrable (fun ω => ((τ ω).untopA : ℝ) * X.σ^2) P ∧
      (∫ ω, (stoppedValue M τ ω)^2 ∂P) =
        ∫ ω, ((τ ω).untopA : ℝ) * X.σ^2 ∂P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let M : ℝ≥0 → Ω → ℝ := fun t ω => X.X t ω - (t : ℝ) * X.c
  let A : ℝ≥0 → Ω → ℝ := fun t _ => (t : ℝ) * X.σ^2
  change Integrable (fun ω => A (τ ω).untopA ω) P ∧
    (∫ ω, (stoppedValue M τ ω)^2 ∂P) =
      ∫ ω, A (τ ω).untopA ω ∂P
  have hM : Martingale M 𝓕.rightCont P :=
    avram_wave6_03_original_rightCont_zerojump_centered_source_martingale X hν
  have hQ : Martingale (fun t ω => (M t ω)^2 - A t ω) 𝓕.rightCont P :=
    avram_wave6_03_original_rightCont_zerojump_centered_source_square_martingale X hν
  have hMom :=
    avram_a21_original_zero_jump_process_fixed_time_square_moment_20261113 X hν T
  have hMMeas : Measurable (M T) := by
    change Measurable (fun ω => X.X T ω - (T : ℝ) * X.c)
    exact ((X.adapted T).mono (𝓕.le T) le_rfl).sub_const _
  have hM2 : MemLp (M T) 2 P :=
    (memLp_two_iff_integrable_sq (μ := P)
      hMMeas.aestronglyMeasurable).2 hMom.1
  have hQTzero : (∫ ω, (M T ω)^2 - A T ω ∂P) = 0 := by
    change (∫ ω, (M T ω)^2 - (T : ℝ) * X.σ^2 ∂P) = 0
    rw [integral_sub hMom.1 (integrable_const _), hMom.2]
    simp
  exact avram_lsv_finite_grid_stopped_quadratic_energy_isometry
    P 𝓕.rightCont M A hM hQ T hM2 hQTzero τ hτ hτle hτcount

