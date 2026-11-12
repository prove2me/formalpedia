-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb51_sigma_zero_original_quadratic_cell_fourth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T11:38:56.114766+00:00
-- url     : https://prove2.me/submissions/cbf9c5d6-9c1d-4d98-b123-f155773edf62

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_nojump_nogaussian_drift_increment_ae
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Pure drift is the zero-fourth-moment endpoint of the original
centred Gaussian mesh estimate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hν : X.ν = 0) (hσ : X.σ = 0) (n : ℕ) (hn : 0 < n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m : ℕ) (i : ℕ), i ∈ Finset.range (m + 1) →
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      let R : Ω → ℝ := fun ω =>
        (X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c) ^ 2 -
          (Δ : ℝ) * X.σ ^ 2
      Integrable (fun ω => (R ω) ^ 2) P ∧
        (∫ ω, (R ω) ^ 2 ∂P) ≤ K / (((m + 1 : ℕ) : ℝ) ^ 2) := by
  letI : IsProbabilityMeasure P := X.isProbability
  refine ⟨0, le_refl _, ?_⟩
  intro m i hi
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
  let s : ℝ≥0 := (i : ℝ≥0) * Δ
  let R : Ω → ℝ := fun ω =>
    (X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c) ^ 2 -
      (Δ : ℝ) * X.σ ^ 2
  change Integrable (fun ω => (R ω) ^ 2) P ∧
    (∫ ω, (R ω) ^ 2 ∂P) ≤
      (0 : ℝ) / (((m + 1 : ℕ) : ℝ) ^ 2)
  have hτ : IsStoppingTime 𝓕.rightCont
      (fun _ : Ω => (s : WithTop ℝ≥0)) :=
    isStoppingTime_const 𝓕.rightCont s
  have hz :=
    avram_wave5_03a_actual_rightCont_stopped_nojump_nogaussian_drift_increment_ae
      X hν hσ (fun _ : Ω => s) hτ s (by intro ω; exact le_rfl) Δ
  have heq : (fun ω => (R ω) ^ 2) =ᵐ[P] (fun _ => (0 : ℝ)) := by
    filter_upwards [hz] with ω hω
    dsimp [R]
    simp [hσ, hω]
  have hint : Integrable (fun ω => (R ω) ^ 2) P :=
    (integrable_const (0 : ℝ)).congr heq.symm
  refine ⟨hint, ?_⟩
  have he : (∫ ω, (R ω) ^ 2 ∂P) = 0 := by
    rw [integral_congr_ae heq]
    simp
  simp [he]
