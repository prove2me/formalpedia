-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_negative_band_actual_jump_sum_collision_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:08:34.081852+00:00
-- url     : https://prove2.me/submissions/303f1365-bb65-4da8-8733-aa2298899d42

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
    (f : Ω → ℝ≥0 → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ ω u, |f ω u| ≤ B)
    (hErrSquareMeas : AEStronglyMeasurable (fun ω =>
      (if 2 ≤ {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard then
        ∑ u ∈ (avram_wave7_06_original_negative_band_marked_times_finite
          X ω T n).toFinset, f ω u
      else 0) ^ 2) P) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let K : Ω → ℕ := fun ω => {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => (if 2 ≤ K ω then ∑ u ∈ F ω, f ω u else 0) ^ 2) P ∧
    (∫ ω, (if 2 ≤ K ω then ∑ u ∈ F ω, f ω u else 0) ^ 2 ∂P) ≤
      2 * B ^ 2 * r ^ 2 := by
  classical
  let F : Ω → Finset ℝ≥0 := fun ω =>
    (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
  let K : Ω → ℕ := fun ω => {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
  let r : ℝ :=
    ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
  let E : Ω → ℝ := fun ω =>
    if 2 ≤ K ω then ∑ u ∈ F ω, f ω u else 0
  let J : Ω → ℝ := fun ω => if 2 ≤ K ω then (K ω : ℝ) else 0
  let S : Ω → ℝ := fun ω => if 2 ≤ K ω then (K ω : ℝ) ^ 2 else 0
  let Q : Ω → ℝ := fun ω => (E ω) ^ 2
  change Integrable Q P ∧ (∫ ω, Q ω ∂P) ≤ 2 * B ^ 2 * r ^ 2
  have hSquare :=
    avram_p4_s3_original_negative_band_collision_second_moment_quadratic X T n
  change Integrable S P ∧ (∫ ω, S ω ∂P) ≤ 2 * r ^ 2 at hSquare
  have hFcard (ω : Ω) : (F ω).card = K ω := by
    let s : Set ℝ≥0 := {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}
    have hs : s.Finite :=
      avram_wave7_06_original_negative_band_marked_times_finite X ω T n
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
  have hJnn (ω : Ω) : 0 ≤ J ω := by
    dsimp [J]
    split_ifs <;> positivity
  have hSnn (ω : Ω) : 0 ≤ S ω := by
    dsimp [S]
    split_ifs <;> positivity
  have hJSq (ω : Ω) : J ω ^ 2 = S ω := by
    dsimp [J,S]
    split_ifs <;> ring
  have hQMeas : AEStronglyMeasurable Q P := by
    simpa only [Q,E,F,K] using hErrSquareMeas
  have hPoint (ω : Ω) : Q ω ≤ B ^ 2 * S ω := by
    have hAbs : |E ω| ≤ B * J ω := by
      simpa only [Real.norm_eq_abs] using hDom ω
    have hBJnn : 0 ≤ B * J ω := mul_nonneg hB (hJnn ω)
    have hDiff : 0 ≤ B * J ω - |E ω| := sub_nonneg.mpr hAbs
    have hSum : 0 ≤ B * J ω + |E ω| :=
      add_nonneg hBJnn (abs_nonneg _)
    have hSq : (E ω) ^ 2 ≤ (B * J ω) ^ 2 := by
      nlinarith [mul_nonneg hDiff hSum, sq_abs (E ω)]
    calc
      Q ω = (E ω) ^ 2 := rfl
      _ ≤ (B * J ω) ^ 2 := hSq
      _ = B ^ 2 * S ω := by rw [mul_pow, hJSq ω]
  have hNormDom (ω : Ω) : ‖Q ω‖ ≤ ‖B ^ 2 * S ω‖ := by
    have hQnn : 0 ≤ Q ω := by dsimp [Q]; positivity
    have hBnn : 0 ≤ B ^ 2 * S ω :=
      mul_nonneg (sq_nonneg B) (hSnn ω)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hQnn,
      abs_of_nonneg hBnn] using hPoint ω
  have hBInt : Integrable (fun ω => B ^ 2 * S ω) P :=
    hSquare.1.const_mul (B ^ 2)
  have hQInt : Integrable Q P :=
    hBInt.mono hQMeas (Filter.Eventually.of_forall hNormDom)
  refine ⟨hQInt, ?_⟩
  calc
    (∫ ω, Q ω ∂P) ≤ ∫ ω, B ^ 2 * S ω ∂P :=
      integral_mono_ae hQInt hBInt (Filter.Eventually.of_forall hPoint)
    _ = B ^ 2 * ∫ ω, S ω ∂P := integral_const_mul (B ^ 2) _
    _ ≤ B ^ 2 * (2 * r ^ 2) :=
      mul_le_mul_of_nonneg_left hSquare.2 (sq_nonneg B)
    _ = 2 * B ^ 2 * r ^ 2 := by ring
