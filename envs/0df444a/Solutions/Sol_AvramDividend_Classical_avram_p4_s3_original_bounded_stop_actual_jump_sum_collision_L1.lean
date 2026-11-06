-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_bounded_stop_actual_jump_sum_collision_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:08:48.537919+00:00
-- url     : https://prove2.me/submissions/1b601130-67a2-4789-a4bf-42040c185fae

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_collision_mass_quadratic

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
          -(1 / ((n : ℝ) + 1))}.ncard))
    (f : Ω → ℝ≥0 → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ ω u, |f ω u| ≤ B)
    (hErrMeas : AEStronglyMeasurable (fun ω =>
      if 2 ≤ {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard then
        ∑ u ∈ (avram_wave7_06_original_negative_band_marked_times_finite
          X ω (τ ω) n).toFinset, f ω u
      else 0) P) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω (τ ω) n).toFinset
    let K : Ω → ℕ := fun ω => {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => if 2 ≤ K ω then ∑ u ∈ F ω, f ω u else 0) P ∧
    (∫ ω, ‖if 2 ≤ K ω then ∑ u ∈ F ω, f ω u else 0‖ ∂P) ≤ B * r ^ 2 := by
  classical
  let F : Ω → Finset ℝ≥0 := fun ω =>
    (avram_wave7_06_original_negative_band_marked_times_finite X ω (τ ω) n).toFinset
  let K : Ω → ℕ := fun ω => {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
  let r : ℝ :=
    ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
  let E : Ω → ℝ := fun ω =>
    if 2 ≤ K ω then ∑ u ∈ F ω, f ω u else 0
  let J : Ω → ℝ := fun ω => if 2 ≤ K ω then (K ω : ℝ) else 0
  change Integrable E P ∧ (∫ ω, ‖E ω‖ ∂P) ≤ B * r ^ 2
  have hCollision := avram_p4_s3_original_bounded_stop_negative_band_collision_mass_quadratic X T n τ hτ hKmeas
  change Integrable J P ∧ (∫ ω, J ω ∂P) ≤ r ^ 2 at hCollision
  have hFcard (ω : Ω) : (F ω).card = K ω := by
    let s : Set ℝ≥0 := {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}
    have hs : s.Finite :=
      avram_wave7_06_original_negative_band_marked_times_finite X ω (τ ω) n
    have hCard : s.ncard = hs.toFinset.card :=
      Set.ncard_eq_toFinset_card s hs
    simpa only [F,K,s] using hCard.symm
  have hSumBound (ω : Ω) :
      ‖∑ u ∈ F ω, f ω u‖ ≤ B * (K ω : ℝ) := by
    calc
      ‖∑ u ∈ F ω, f ω u‖ ≤ ∑ u ∈ F ω, ‖f ω u‖ :=
        norm_sum_le (F ω) (f ω)
      _ ≤ ∑ u ∈ F ω, B := by
        apply Finset.sum_le_sum
        intro u hu
        simpa only [Real.norm_eq_abs] using hf ω u
      _ = B * ((F ω).card : ℝ) := by simp [mul_comm]
      _ = B * (K ω : ℝ) := by rw [hFcard ω]
  have hDom (ω : Ω) : ‖E ω‖ ≤ B * J ω := by
    dsimp [E,J]
    by_cases hk : 2 ≤ K ω
    · simp only [if_pos hk]
      exact hSumBound ω
    · simp [hk]
  have hGInt : Integrable (fun ω => B * J ω) P :=
    hCollision.1.const_mul B
  have hJnn (ω : Ω) : 0 ≤ J ω := by
    dsimp [J]
    split_ifs <;> positivity
  have hGnn (ω : Ω) : 0 ≤ B * J ω :=
    mul_nonneg hB (hJnn ω)
  have hDomNorm (ω : Ω) : ‖E ω‖ ≤ ‖B * J ω‖ := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hGnn ω)] using hDom ω
  have hEInt : Integrable E P :=
    hGInt.mono (by simpa only [E,K,F] using hErrMeas)
      (Filter.Eventually.of_forall hDomNorm)
  refine ⟨hEInt, ?_⟩
  calc
    (∫ ω, ‖E ω‖ ∂P) ≤ ∫ ω, B * J ω ∂P :=
      integral_mono_ae
        (f := fun ω => ‖E ω‖) (g := fun ω => B * J ω)
        hEInt.norm hGInt (Filter.Eventually.of_forall hDom)
    _ = B * ∫ ω, J ω ∂P := integral_const_mul B _
    _ ≤ B * r ^ 2 := mul_le_mul_of_nonneg_left hCollision.2 hB
