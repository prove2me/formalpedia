-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_collision_second_moment_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:01:51.14651+00:00
-- url     : https://prove2.me/submissions/3f17d5c8-983d-4c2b-b132-da2198996a2b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_band_collision_second_moment_quadratic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (hKmeas : Measurable (fun ω : Ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard)) :
    let K : Ω → ℕ := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => if 2 ≤ K ω then (K ω : ℝ) ^ 2 else 0) P ∧
    (∫ ω, (if 2 ≤ K ω then (K ω : ℝ) ^ 2 else 0) ∂P) ≤
      2 * r ^ 2 := by
  classical
  let K : Ω → ℕ := fun ω =>
    {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard
  let KT : Ω → ℕ := fun ω =>
    {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard
  let r : ℝ :=
    ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
  let E : Ω → ℝ := fun ω => if 2 ≤ K ω then (K ω : ℝ) ^ 2 else 0
  let ET : Ω → ℝ := fun ω => if 2 ≤ KT ω then (KT ω : ℝ) ^ 2 else 0
  change Integrable E P ∧ (∫ ω, E ω ∂P) ≤ 2 * r ^ 2
  have hFull := avram_p4_s3_original_negative_band_collision_second_moment_quadratic
    X T n
  change Integrable ET P ∧ (∫ ω, ET ω ∂P) ≤ 2 * r ^ 2 at hFull
  have hKle (ω : Ω) : K ω ≤ KT ω := by
    apply Set.ncard_le_ncard
    · intro u hu
      exact ⟨hu.1, (hu.2.1).trans (hτ ω), hu.2.2⟩
    · exact avram_wave7_06_original_negative_band_marked_times_finite X ω T n
  have hMeasTransform : Measurable (fun k : ℕ =>
      if 2 ≤ k then (k : ℝ) ^ 2 else 0) := measurable_of_countable _
  have hMeas : AEStronglyMeasurable E P := by
    have hm : Measurable E := by
      change Measurable (fun ω => (fun k : ℕ =>
        if 2 ≤ k then (k : ℝ) ^ 2 else 0) (K ω))
      exact hMeasTransform.comp hKmeas
    exact hm.aestronglyMeasurable
  have hEnn (ω : Ω) : 0 ≤ E ω := by
    dsimp [E]
    split_ifs <;> positivity
  have hTnn (ω : Ω) : 0 ≤ ET ω := by
    dsimp [ET]
    split_ifs <;> positivity
  have hPoint (ω : Ω) : E ω ≤ ET ω := by
    by_cases hk : 2 ≤ K ω
    · have ht : 2 ≤ KT ω := le_trans hk (hKle ω)
      simp only [E, ET, if_pos hk, if_pos ht]
      gcongr
      exact_mod_cast hKle ω
    · simp only [E, if_neg hk]
      exact hTnn ω
  have hNorm (ω : Ω) : ‖E ω‖ ≤ ‖ET ω‖ := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hEnn ω),
      abs_of_nonneg (hTnn ω)] using hPoint ω
  have hIntegrable : Integrable E P :=
    hFull.1.mono hMeas (Filter.Eventually.of_forall hNorm)
  refine ⟨hIntegrable, ?_⟩
  exact (integral_mono_ae hIntegrable hFull.1
    (Filter.Eventually.of_forall hPoint)).trans hFull.2
