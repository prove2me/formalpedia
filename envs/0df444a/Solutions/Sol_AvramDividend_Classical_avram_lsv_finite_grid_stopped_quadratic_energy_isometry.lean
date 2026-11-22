-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsv_finite_grid_stopped_quadratic_energy_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T13:01:56.129442+00:00
-- url     : https://prove2.me/submissions/14d77230-32f0-446b-a4dc-c34e84becafb

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_lsv_finite_grid_stopping_square_le
import Theorems.Thm_AvramDividend_Classical_avram_lsv_finite_grid_stopped_martingale_expectation

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
noncomputable section

/- Direct synthesis of dufeteller/lean-lsv
   LSV/LocalizedStoppingL2Convergence.lean and
   LSV/LocalizedOptionalExpectation.lean:
   actual finite-grid stopped martingale mean-square energy equals its
   stopped quadratic compensator. Original CC BY 4.0,
   source commit a5f604de2e1ae431de4cbecde23e5694a12ba719.
   Neither a Brownian driver nor an unproved identity is hypothesised. -/

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (M A : ℝ≥0 → Ω → ℝ)
    (hM : Martingale M ℱ μ)
    (hQ : Martingale (fun t ω => (M t ω)^2 - A t ω) ℱ μ)
    (T : ℝ≥0) (hM2 : MemLp (M T) 2 μ)
    (hQTzero : (∫ ω, (M T ω)^2 - A T ω ∂μ) = 0)
    (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime ℱ τ)
    (hτle : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hτcount : (Set.range τ).Countable) :
    Integrable (fun ω => A (τ ω).untopA ω) μ ∧
      (∫ ω, (stoppedValue M τ ω)^2 ∂μ) =
        ∫ ω, A (τ ω).untopA ω ∂μ := by
  let Q : ℝ≥0 → Ω → ℝ := fun t ω => (M t ω)^2 - A t ω
  have hS :=
    avram_lsv_finite_grid_stopping_square_le
      μ ℱ M hM T hM2 τ hτ hτle hτcount
  have hOp :=
    avram_lsv_finite_grid_stopped_martingale_expectation
      μ ℱ Q hQ T τ hτ hτle hτcount
  have hAexpr : (fun ω => A (τ ω).untopA ω) =
      (fun ω => (stoppedValue M τ ω)^2) - stoppedValue Q τ := by
    funext ω
    dsimp [Q, stoppedValue]
    ring
  have hAi : Integrable (fun ω => A (τ ω).untopA ω) μ := by
    rw [hAexpr]
    exact hS.1.integrable_sq.sub hOp.1
  refine ⟨hAi, ?_⟩
  have hQstop : (∫ ω, stoppedValue Q τ ω ∂μ) = 0 :=
    hOp.2.trans hQTzero
  have hQexpr : (fun ω => stoppedValue Q τ ω) =
      (fun ω => (stoppedValue M τ ω)^2 - A (τ ω).untopA ω) := by
    funext ω
    rfl
  rw [hQexpr, integral_sub hS.1.integrable_sq hAi] at hQstop
  exact sub_eq_zero.mp hQstop

