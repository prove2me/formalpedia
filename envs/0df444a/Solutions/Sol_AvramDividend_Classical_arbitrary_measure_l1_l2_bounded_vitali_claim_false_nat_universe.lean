-- Prove2me | solution 1 for AvramDividend.Classical.arbitrary_measure_l1_l2_bounded_vitali_claim_false_nat_universe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T11:00:25.040758+00:00
-- url     : https://prove2.me/submissions/2509d824-00a2-44dd-80f9-1b123e6b78db

import Mathlib
import Theorems.Thm_AvramDividend_Classical_counting_delta_indicator_mean_and_pointwise_zero
import Theorems.Thm_AvramDividend_Classical_counting_delta_l1_l2_norm_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
open scoped NNReal ENNReal
noncomputable section
theorem solution :
    ¬ (∀ {Ω : Type} [MeasurableSpace Ω]
      (μ : Measure Ω) (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
      (B D : ℝ≥0),
      (∀ n, AEStronglyMeasurable (Y n) μ) →
      (∀ n, eLpNorm (Y n) 2 μ ≤ (B : ENNReal)) →
      (∀ n, eLpNorm (Y n) 1 μ ≤ (D : ENNReal)) →
      (∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) →
      Integrable Z μ ∧
        Tendsto (fun n => ∫ ω, Y n ω ∂μ) atTop
          (nhds (∫ ω, Z ω ∂μ))) := by
  intro h
  let Y : ℕ → ℕ → ℝ := fun n => ({n} : Set ℕ).indicator (fun _ => 1)
  have hZeroAndMean :=
    AvramDividend.Classical.counting_delta_indicator_mean_and_pointwise_zero
  have hNorm := AvramDividend.Classical.counting_delta_l1_l2_norm_one
  have hYm : ∀ n, AEStronglyMeasurable (Y n) (Measure.count : Measure ℕ) := by
    intro n
    exact (measurable_const.indicator (measurableSet_singleton n)).aestronglyMeasurable
  have hTwo : ∀ n, eLpNorm (Y n) 2 (Measure.count : Measure ℕ) ≤
      ((1 : ℝ≥0) : ENNReal) := by
    intro n
    simpa only [ENNReal.coe_one] using le_of_eq (hNorm n).2
  have hOne : ∀ n, eLpNorm (Y n) 1 (Measure.count : Measure ℕ) ≤
      ((1 : ℝ≥0) : ENNReal) := by
    intro n
    simpa only [ENNReal.coe_one] using le_of_eq (hNorm n).1
  obtain ⟨_, hConv⟩ := h (Measure.count : Measure ℕ) Y
    (fun _ : ℕ => (0 : ℝ)) 1 1 hYm hTwo hOne (Filter.Eventually.of_forall hZeroAndMean.2)
  have hZero : (∫ ω : ℕ, (0 : ℝ) ∂(Measure.count : Measure ℕ)) = 0 := by
    simp
  rw [hZero] at hConv
  have hMean :
      (fun n => ∫ ω, Y n ω ∂(Measure.count : Measure ℕ)) =
        (fun _ : ℕ => (1 : ℝ)) := funext hZeroAndMean.1
  rw [hMean] at hConv
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hConv)
