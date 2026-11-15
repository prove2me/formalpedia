-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_stopped_bounded_predictable_smallmark_grid_common_integrable_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:53:52.3802+00:00
-- url     : https://prove2.me/submissions/05a34550-a8d5-4af7-a4c4-98d10ea6ae64

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_intrinsic_smallmark_true_stopped_chronological_grid_uniform_L1_variation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
        atTop (𝓝 (Jsmall t ω)))
    (T : ℝ≥0) (L : ℝ) (hL : 0 ≤ L) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Ioo (-1 : ℝ) 0)
    let B : Ω → ℝ := fun ω => (N ω).toReal +
      (T : ℝ) * ‖∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν‖
    Integrable (fun ω => L * B ω) P ∧
      ∀ᵐ ω ∂P, ∀ (n : ℕ) (t : ℕ → ℝ≥0)
        (σ : Ω → ℝ≥0) (W : ℕ → Ω → ℝ),
        Monotone t → t n ≤ T →
        (∀ i ∈ Finset.range n, ∀ ω', ‖W i ω'‖ ≤ L) →
        ‖∑ i ∈ Finset.range n, W i ω *
          (Jsmall (min (t (i + 1)) (σ ω)) ω -
            Jsmall (min (t i) (σ ω)) ω)‖ ≤ L * B ω := by
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Ioo (-1 : ℝ) 0)
  let B : Ω → ℝ := fun ω => (N ω).toReal +
    (T : ℝ) * ‖∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν‖
  change Integrable (fun ω => L * B ω) P ∧
    ∀ᵐ ω ∂P, ∀ (n : ℕ) (t : ℕ → ℝ≥0)
      (σ : Ω → ℝ≥0) (W : ℕ → Ω → ℝ),
      Monotone t → t n ≤ T →
      (∀ i ∈ Finset.range n, ∀ ω', ‖W i ω'‖ ≤ L) →
      ‖∑ i ∈ Finset.range n, W i ω *
        (Jsmall (min (t (i + 1)) (σ ω)) ω -
          Jsmall (min (t i) (σ ω)) ω)‖ ≤ L * B ω
  have hSource :=
    AvramDividend.Classical.avram_b24_original_intrinsic_smallmark_true_stopped_chronological_grid_uniform_L1_variation
      X hFinite Jsmall hJsource T
  change Integrable B P ∧
    (∀ᵐ ω ∂P, ∀ (n : ℕ) (t : ℕ → ℝ≥0)
      (σ : Ω → ℝ≥0), Monotone t → t n ≤ T →
      (∑ i ∈ Finset.range n,
        ‖Jsmall (min (t (i + 1)) (σ ω)) ω -
          Jsmall (min (t i) (σ ω)) ω‖) ≤ B ω)
    at hSource
  refine ⟨hSource.1.const_mul L, ?_⟩
  filter_upwards [hSource.2] with ω hω
  intro n t σ W hmono hT hW
  have hSourceBound := hω n t σ hmono hT
  calc
    ‖∑ i ∈ Finset.range n, W i ω *
      (Jsmall (min (t (i + 1)) (σ ω)) ω -
        Jsmall (min (t i) (σ ω)) ω)‖ ≤
      ∑ i ∈ Finset.range n,
        ‖W i ω *
          (Jsmall (min (t (i + 1)) (σ ω)) ω -
            Jsmall (min (t i) (σ ω)) ω)‖ :=
      norm_sum_le (Finset.range n) _
    _ ≤ ∑ i ∈ Finset.range n, L *
        ‖Jsmall (min (t (i + 1)) (σ ω)) ω -
          Jsmall (min (t i) (σ ω)) ω‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hW i hi ω) (norm_nonneg _)
    _ = L * (∑ i ∈ Finset.range n,
        ‖Jsmall (min (t (i + 1)) (σ ω)) ω -
          Jsmall (min (t i) (σ ω)) ω‖) := by
      rw [Finset.mul_sum]
    _ ≤ L * B ω :=
      mul_le_mul_of_nonneg_left hSourceBound hL
