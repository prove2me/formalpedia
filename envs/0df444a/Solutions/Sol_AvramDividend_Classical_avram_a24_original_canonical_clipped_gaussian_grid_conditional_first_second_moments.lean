-- Prove2me | solution 1 for AvramDividend.Classical.avram_a24_original_canonical_clipped_gaussian_grid_conditional_first_second_moments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:38:59.55246+00:00
-- url     : https://prove2.me/submissions/68fb5f3d-9be3-40fb-b156-bbe54556b8e2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_canonical_gaussian_grid_joint_stop_and_horizon
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_condExp_mean_variance
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact physical conditional Gaussian moments for every clipped uniform cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (n : ℕ) (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0)) :
    ∀ j i : ℕ,
      let δ : ℝ≥0 := (n : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)
      let τg : Ω → ℝ≥0 := fun ω => min ((i : ℝ≥0) * δ) (σ ω)
      let hτg : ∀ s : ℝ≥0,
        MeasurableSet[𝓕.rightCont s] {ω : Ω | τg ω ≤ s} :=
        (avram_a24_original_canonical_gaussian_grid_joint_stop_and_horizon
          σ hσstop n hσbound).1 j i
      let M : Ω → ℝ := fun ω =>
        X.X (τg ω + δ) ω - X.X (τg ω) ω - (δ : ℝ) * X.c
      Integrable M P ∧
      (P[M | (isStoppingTime_withTop_of_le_events τg hτg).measurableSpace]
        =ᵐ[P] (fun _ => (0 : ℝ))) ∧
      Integrable (fun ω => M ω ^ 2) P ∧
      (P[(fun ω => M ω ^ 2) |
        (isStoppingTime_withTop_of_le_events τg hτg).measurableSpace]
        =ᵐ[P] (fun _ => (δ : ℝ) * X.σ ^ 2)):= by
  intro j i
  dsimp
  exact avram_wave6_03_original_rightCont_stopped_gaussian_condExp_mean_variance
    X hν
    (fun ω => min ((i : ℝ≥0) *
      ((n : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0))) (σ ω))
    ((avram_a24_original_canonical_gaussian_grid_joint_stop_and_horizon
      σ hσstop n hσbound).1 j i)
    (n : ℝ≥0)
    ((avram_a24_original_canonical_gaussian_grid_joint_stop_and_horizon
      σ hσstop n hσbound).2.1 j i)
    ((n : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0))
