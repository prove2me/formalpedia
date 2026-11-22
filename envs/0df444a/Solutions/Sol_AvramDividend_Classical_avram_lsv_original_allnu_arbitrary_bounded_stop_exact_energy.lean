-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsv_original_allnu_arbitrary_bounded_stop_exact_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T13:44:21.156288+00:00
-- url     : https://prove2.me/submissions/d3699af5-f2e1-4630-a6a2-3d60d8ae14b4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_lsv_original_zerojump_arbitrary_bounded_stop_exact_energy

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
noncomputable section

/- Genuine original mixed Levy process with actual same-space zero-jump Gaussian
   channel. The physical decomposition by small/large jumps is required.
   dufeteller lean-lsv CC BY 4.0, commit a5f604d. -/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c +
        (Y.X t ω - (t : ℝ) * Y.c) + Jsmall t ω + Jlarge t ω)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (hτmeas : Measurable (fun ω => (τ ω : ℝ))) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    Integrable (fun ω => (M (τ ω) ω)^2) P ∧
      (∫ ω, (M (τ ω) ω)^2 ∂P) =
        ∫ ω, (τ ω : ℝ) * X.σ^2 ∂P := by
  classical
  let M : ℝ≥0 → Ω → ℝ := fun t ω =>
    X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
  change Integrable (fun ω => (M (τ ω) ω)^2) P ∧
    (∫ ω, (M (τ ω) ω)^2 ∂P) =
      ∫ ω, (τ ω : ℝ) * X.σ^2 ∂P
  have hMstopEq : ∀ ω,
      M (τ ω) ω = Y.X (τ ω) ω - (τ ω : ℝ) * Y.c := by
    intro ω
    dsimp [M]
    rw [hSourceDecomp (τ ω) ω]
    ring
  have hSquareEq : (fun ω => (M (τ ω) ω)^2) =
      (fun ω => (Y.X (τ ω) ω - (τ ω : ℝ) * Y.c)^2) := by
    funext ω
    rw [hMstopEq ω]
  rw [hSquareEq, ← hYσ]
  exact avram_lsv_original_zerojump_arbitrary_bounded_stop_exact_energy
    Y hYν n hn τ hτstop hτbound hτmeas

