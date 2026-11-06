-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_negative_band_bounded_collision_weighted_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T11:53:36.3892+00:00
-- url     : https://prove2.me/submissions/1aa95aab-75ed-42dd-886a-4e329fe293d8

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_band_collision_second_moment_quadratic
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_original_negative_band_ncard_measurable

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
    (H : Ω → ℝ) (hHm : Measurable H)
    (B : ℝ) (hB : 0 ≤ B) (hH : ∀ ω, |H ω| ≤ B) :
    let K : Ω → ℕ := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω =>
      (H ω * (if 2 ≤ K ω then (K ω : ℝ) else 0)) ^ 2) P ∧
    (∫ ω, (H ω * (if 2 ≤ K ω then (K ω : ℝ) else 0)) ^ 2 ∂P) ≤
      2 * B ^ 2 * r ^ 2 := by
  classical
  let K : Ω → ℕ := fun ω =>
    {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard
  let r : ℝ :=
    ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
  let J : Ω → ℝ := fun ω => if 2 ≤ K ω then (K ω : ℝ) else 0
  let S : Ω → ℝ := fun ω => if 2 ≤ K ω then (K ω : ℝ) ^ 2 else 0
  let Q : Ω → ℝ := fun ω => (H ω * J ω) ^ 2
  change Integrable Q P ∧ (∫ ω, Q ω ∂P) ≤ 2 * B ^ 2 * r ^ 2
  have hSquare := avram_p4_s3_original_negative_band_collision_second_moment_quadratic
    X T n
  change Integrable S P ∧ (∫ ω, S ω ∂P) ≤ 2 * r ^ 2 at hSquare
  have hm : Measurable K := avram_p4_f2_original_negative_band_ncard_measurable X T n
  have hEvent : MeasurableSet {ω : Ω | 2 ≤ K ω} := by
    change MeasurableSet (K ⁻¹' (Ici (2 : ℕ)))
    exact hm measurableSet_Ici
  have hJm : Measurable J := by
    dsimp [J]
    have hNatCast : Measurable (fun z : ℕ => (z : ℝ)) :=
      measurable_of_countable _
    have hCast : Measurable (fun ω => (K ω : ℝ)) :=
      hNatCast.comp hm
    exact hCast.ite hEvent measurable_const
  have hQMeas : AEStronglyMeasurable Q P := by
    have h : Measurable Q := (hHm.mul hJm).pow_const 2
    exact h.aestronglyMeasurable
  have hSnn (ω : Ω) : 0 ≤ S ω := by
    dsimp [S]
    split_ifs <;> positivity
  have hJSq (ω : Ω) : J ω ^ 2 = S ω := by
    dsimp [J,S]
    split_ifs <;> ring
  have hHSq (ω : Ω) : (H ω) ^ 2 ≤ B ^ 2 := by
    have hd : 0 ≤ B - |H ω| := sub_nonneg.mpr (hH ω)
    have hp : 0 ≤ B + |H ω| := add_nonneg hB (abs_nonneg _)
    nlinarith [mul_nonneg hd hp, sq_abs (H ω)]
  have hPoint (ω : Ω) : Q ω ≤ B ^ 2 * S ω := by
    dsimp [Q]
    rw [mul_pow, hJSq ω]
    exact mul_le_mul_of_nonneg_right (hHSq ω) (hSnn ω)
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
