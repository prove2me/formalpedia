-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_bounded_stopped_negative_band_weighted_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T09:57:06.024126+00:00
-- url     : https://prove2.me/submissions/8942d29d-741a-47ac-a4b0-2a21ec9636b3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_square_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A bounded original-state weight preserves the physical stopped band's
exact square-energy envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (hKmeas : Measurable (fun ω : Ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard))
    (H : Ω → ℝ) (hHm : Measurable H)
    (B : ℝ) (hB : 0 ≤ B) (hH : ∀ ω, |H ω| ≤ B) :
    let K : Ω → ℕ := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => (H ω * (K ω : ℝ)) ^ 2) P ∧
      (∫ ω, (H ω * (K ω : ℝ)) ^ 2 ∂P) ≤ B ^ 2 * (r ^ 2 + r) := by
  let K : Ω → ℕ := fun ω =>
    {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard
  let r : ℝ :=
    ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
  change Integrable (fun ω => (H ω * (K ω : ℝ)) ^ 2) P ∧
    (∫ ω, (H ω * (K ω : ℝ)) ^ 2 ∂P) ≤ B ^ 2 * (r ^ 2 + r)
  have hCount := avram_p4_s3_original_bounded_stop_negative_band_square_budget
    X T n τ hτ hKmeas
  change Integrable (fun ω => (K ω : ℝ) ^ 2) P ∧
    (∫ ω, (K ω : ℝ) ^ 2 ∂P) ≤ r ^ 2 + r at hCount
  have hKmeas' : Measurable K := hKmeas
  have hKreal : Measurable (fun ω => (K ω : ℝ)) :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp hKmeas'
  have hMeas : Measurable (fun ω => (H ω * (K ω : ℝ)) ^ 2) :=
    (hHm.mul hKreal).pow_const 2
  have hPointwise (ω : Ω) :
      (H ω * (K ω : ℝ)) ^ 2 ≤ B ^ 2 * (K ω : ℝ) ^ 2 := by
    have hBound := abs_le.mp (hH ω)
    have hMul : 0 ≤ (B - H ω) * (B + H ω) :=
      mul_nonneg (by linarith) (by linarith)
    have hSq : (H ω) ^ 2 ≤ B ^ 2 := by nlinarith
    have hTimes := mul_le_mul_of_nonneg_right hSq
      (sq_nonneg (K ω : ℝ))
    nlinarith [hTimes]
  have hMajorant : Integrable (fun ω => B ^ 2 * (K ω : ℝ) ^ 2) P :=
    hCount.1.const_mul (B ^ 2)
  have hWeighted : Integrable (fun ω => (H ω * (K ω : ℝ)) ^ 2) P := by
    apply Integrable.mono hMajorant hMeas.aestronglyMeasurable
    filter_upwards [] with ω
    change ‖(H ω * (K ω : ℝ)) ^ 2‖ ≤ ‖B ^ 2 * (K ω : ℝ) ^ 2‖
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact hPointwise ω
  refine ⟨hWeighted, ?_⟩
  have hMeanLe := integral_mono_ae hWeighted hMajorant
    (Filter.Eventually.of_forall hPointwise)
  calc
    (∫ ω, (H ω * (K ω : ℝ)) ^ 2 ∂P)
        ≤ ∫ ω, B ^ 2 * (K ω : ℝ) ^ 2 ∂P := hMeanLe
    _ = B ^ 2 * (∫ ω, (K ω : ℝ) ^ 2 ∂P) := by rw [integral_const_mul]
    _ ≤ B ^ 2 * (r ^ 2 + r) :=
      mul_le_mul_of_nonneg_left hCount.2 (sq_nonneg B)
