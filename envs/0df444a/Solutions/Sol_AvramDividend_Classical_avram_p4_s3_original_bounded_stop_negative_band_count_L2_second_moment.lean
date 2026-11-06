-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_count_L2_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:36:43.276863+00:00
-- url     : https://prove2.me/submissions/038b14c4-3f6b-4528-af1b-f1b263353a64

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_count_L1_first_moment
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_factorial_pair_moment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact original stopped count L2 envelope from first and factorial pair moments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (hKmeas : Measurable (fun ω : Ω => {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard)) :
    let K : Ω → ℕ := fun ω => {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => (K ω : ℝ) ^ 2) P ∧
    (∫ ω, (K ω : ℝ) ^ 2 ∂P) ≤ r ^ 2 + r := by
  let K : Ω → ℕ := fun ω => {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard
  let r : ℝ :=
    ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
  change Integrable (fun ω => (K ω : ℝ) ^ 2) P ∧
    (∫ ω, (K ω : ℝ) ^ 2 ∂P) ≤ r ^ 2 + r
  have hFirst :=
    avram_p4_s3_original_bounded_stop_negative_band_count_L1_first_moment
      X T n τ hτ hKmeas
  change Integrable (fun ω => (K ω : ℝ)) P ∧
    (∫ ω, (K ω : ℝ) ∂P) ≤ r at hFirst
  have hFact :=
    avram_p4_s3_original_bounded_stop_negative_band_factorial_pair_moment
      X T n τ hτ hKmeas
  change Integrable (fun ω => (K ω : ℝ) * ((K ω : ℝ) - 1)) P ∧
    (∫ ω, (K ω : ℝ) * ((K ω : ℝ) - 1) ∂P) ≤ r ^ 2 at hFact
  have hIdentity :
      (fun ω : Ω => (K ω : ℝ) ^ 2) =
      (fun ω : Ω => (K ω : ℝ) * ((K ω : ℝ) - 1) + (K ω : ℝ)) := by
    funext ω
    ring
  have hSquare : Integrable (fun ω => (K ω : ℝ) ^ 2) P := by
    rw [hIdentity]
    exact hFact.1.add hFirst.1
  refine ⟨hSquare, ?_⟩
  rw [hIdentity, integral_add hFact.1 hFirst.1]
  exact add_le_add hFact.2 hFirst.2
