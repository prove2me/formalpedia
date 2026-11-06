-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_weighted_L1_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:32:32.710251+00:00
-- url     : https://prove2.me/submissions/7925d06c-aff8-4090-b271-0d589b53b137

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_count_L1_first_moment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A bounded original-process weight times the physical stopped band count
has the exact finite-band first-order L1 estimate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (hKmeas : Measurable (fun ω : Ω => {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard))
    (H : Ω → ℝ) (hHm : Measurable H)
    (B : ℝ) (hB : 0 ≤ B) (hH : ∀ ω, |H ω| ≤ B) :
    let K : Ω → ℕ := fun ω => {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => H ω * (K ω : ℝ)) P ∧
    (∫ ω, |H ω * (K ω : ℝ)| ∂P) ≤ B * r := by
  let K : Ω → ℕ := fun ω => {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard
  let r : ℝ :=
    ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
  change Integrable (fun ω => H ω * (K ω : ℝ)) P ∧
    (∫ ω, |H ω * (K ω : ℝ)| ∂P) ≤ B * r
  have hFirst :=
    avram_p4_s3_original_bounded_stop_negative_band_count_L1_first_moment
      X T n τ hτ hKmeas
  change Integrable (fun ω => (K ω : ℝ)) P ∧
    (∫ ω, (K ω : ℝ) ∂P) ≤ r at hFirst
  have hKmeas' : Measurable K := hKmeas
  have hKreal : Measurable (fun ω => (K ω : ℝ)) :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp hKmeas'
  have hCountNonneg (ω : Ω) : (0 : ℝ) ≤ (K ω : ℝ) :=
    Nat.cast_nonneg (K ω)
  have hBound (ω : Ω) : |H ω * (K ω : ℝ)| ≤ B * (K ω : ℝ) := by
    rw [abs_mul, abs_of_nonneg (hCountNonneg ω)]
    exact mul_le_mul_of_nonneg_right (hH ω) (hCountNonneg ω)
  have hMajor : Integrable (fun ω => B * (K ω : ℝ)) P :=
    hFirst.1.const_mul B
  have hMeas : Measurable (fun ω => H ω * (K ω : ℝ)) :=
    hHm.mul hKreal
  have hWeighted : Integrable (fun ω => H ω * (K ω : ℝ)) P := by
    apply Integrable.mono hMajor hMeas.aestronglyMeasurable
    filter_upwards [] with ω
    change ‖H ω * (K ω : ℝ)‖ ≤ ‖B * (K ω : ℝ)‖
    rw [Real.norm_eq_abs,
      Real.norm_of_nonneg (mul_nonneg hB (hCountNonneg ω))]
    exact hBound ω
  refine ⟨hWeighted, ?_⟩
  have hIntegral := integral_mono_ae hWeighted.abs hMajor
    (Filter.Eventually.of_forall hBound)
  calc
    (∫ ω, |H ω * (K ω : ℝ)| ∂P)
        ≤ ∫ ω, B * (K ω : ℝ) ∂P := hIntegral
    _ = B * (∫ ω, (K ω : ℝ) ∂P) := by rw [integral_const_mul]
    _ ≤ B * r := mul_le_mul_of_nonneg_left hFirst.2 hB
