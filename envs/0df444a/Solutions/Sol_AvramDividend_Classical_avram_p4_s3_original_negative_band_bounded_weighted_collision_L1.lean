-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_negative_band_bounded_weighted_collision_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T08:47:51.022393+00:00
-- url     : https://prove2.me/submissions/9fdc4794-75f7-4a3e-8b41-1a3496947a2a

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_band_collision_mass_quadratic

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
    (H : Ω → ℝ) (hHm : Measurable H) (B : ℝ) (hB : 0 ≤ B)
    (hH : ∀ ω, |H ω| ≤ B) :
    let K : Ω → ℕ := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => H ω * (if 2 ≤ K ω then (K ω : ℝ) else 0)) P ∧
    |∫ ω, H ω * (if 2 ≤ K ω then (K ω : ℝ) else 0) ∂P| ≤ B * r ^ 2 := by
  classical
  let K : Ω → ℕ := fun ω =>
    {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard
  let r : ℝ :=
    ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
  let J : Ω → ℝ := fun ω => if 2 ≤ K ω then (K ω : ℝ) else 0
  change Integrable (fun ω => H ω * J ω) P ∧
    |∫ ω, H ω * J ω ∂P| ≤ B * r ^ 2
  have hCollision :=
    avram_p4_s3_original_negative_band_collision_mass_quadratic X T n
  change Integrable J P ∧ (∫ ω, J ω ∂P) ≤ r ^ 2 at hCollision
  have hJnn (ω : Ω) : 0 ≤ J ω := by
    dsimp [J]
    split_ifs <;> positivity
  have hGInt : Integrable (fun ω => B * J ω) P :=
    hCollision.1.const_mul B
  have hProdAES : AEStronglyMeasurable (fun ω => H ω * J ω) P :=
    hHm.aestronglyMeasurable.mul hCollision.1.aestronglyMeasurable
  have hDom (ω : Ω) : ‖H ω * J ω‖ ≤ ‖B * J ω‖ := by
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hB,
      abs_of_nonneg (hJnn ω)]
    exact mul_le_mul_of_nonneg_right (hH ω) (hJnn ω)
  have hProdI : Integrable (fun ω => H ω * J ω) P :=
    hGInt.mono hProdAES (Filter.Eventually.of_forall hDom)
  refine ⟨hProdI, ?_⟩
  have hDomReal (ω : Ω) : ‖H ω * J ω‖ ≤ B * J ω := by
    simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg hB,
      abs_of_nonneg (hJnn ω)] using hDom ω
  have hIntDom := integral_mono_ae hProdI.norm hGInt
    (Filter.Eventually.of_forall hDomReal)
  have hNorm : |∫ ω, H ω * J ω ∂P| ≤
      ∫ ω, ‖H ω * J ω‖ ∂P := by
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (fun ω => H ω * J ω))
  calc
    |∫ ω, H ω * J ω ∂P| ≤ ∫ ω, ‖H ω * J ω‖ ∂P := hNorm
    _ ≤ ∫ ω, B * J ω ∂P := hIntDom
    _ = B * ∫ ω, J ω ∂P := integral_const_mul B _
    _ ≤ B * r ^ 2 := mul_le_mul_of_nonneg_left hCollision.2 hB
