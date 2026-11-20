-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_actual_physical_source_centered_nonpositive_on_event
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T21:57:15.583487+00:00
-- url     : https://prove2.me/submissions/4d883c95-73e1-496b-9204-6fac81c0e456

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_physical_finite_grid_HJB_generator_Q_nonpositive
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (σ : Ω → ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (m : ℕ → ℕ)
    (A : Set Ω) (Source M Q : ℕ → Ω → ℝ)
    (hQphysical : ∀ j ω,
      Q j ω = (let v : ℕ → ℝ≥0 := fun i => min (u j i) (σ ω)
        let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
        let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
        ∑ i ∈ Finset.range (m j),
          E (v (i + 1)) * (((v (i + 1) - v i : ℝ≥0) : ℝ)) *
            (if 0 < Y (v i) ∧ ENNReal.ofReal (Y (v i)) < C then
              X.generator w (Y (v i)) - q * w (Y (v i))
             else 0)))
    (hMInt : ∀ j, IntegrableOn (M j) A P)
    (hQInt : ∀ j, IntegrableOn (Q j) A P)
    (hMzero : ∀ j, (∫ ω in A, M j ω ∂P) = 0)
    (hSource : ∀ j ω, Source j ω = M j ω + Q j ω) :
    ∀ j, (∫ ω in A, Source j ω ∂P) ≤ 0 := by
  intro j
  have hQsign : ∀ ω, Q j ω ≤ 0 := by
    intro ω
    rw [hQphysical j ω]
    exact avram_jump6_B_original_physical_finite_grid_HJB_generator_Q_nonpositive
      X q w C hw_gen x D σ u m j ω
  have hQmean : (∫ ω in A, Q j ω ∂P) ≤ 0 :=
    MeasureTheory.integral_nonpos hQsign
  have hAE : (fun ω => Source j ω) =ᵐ[P.restrict A]
      (fun ω => M j ω + Q j ω) := by
    filter_upwards [] with ω
    exact hSource j ω
  calc
    (∫ ω in A, Source j ω ∂P) =
        (∫ ω in A, M j ω + Q j ω ∂P) :=
      MeasureTheory.integral_congr_ae hAE
    _ = (∫ ω in A, M j ω ∂P) +
        (∫ ω in A, Q j ω ∂P) :=
      MeasureTheory.integral_add (hMInt j) (hQInt j)
    _ ≤ 0 := by rw [hMzero j]; linarith