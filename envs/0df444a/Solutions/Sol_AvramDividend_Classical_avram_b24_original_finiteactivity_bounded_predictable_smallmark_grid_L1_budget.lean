-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_finiteactivity_bounded_predictable_smallmark_grid_L1_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:49:08.841908+00:00
-- url     : https://prove2.me/submissions/2eaf7826-f347-4f6f-9b6a-d2f5d945077e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_intrinsic_smallmark_deterministic_interval_L1_linear_rate
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
    (S : Finset ℕ) (a b : ℕ → ℝ≥0)
    (hOrd : ∀ i ∈ S, a i ≤ b i)
    (W : ℕ → Ω → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hWBound : ∀ i ∈ S, ∀ ω, ‖W i ω‖ ≤ L)
    (hJM : ∀ i ∈ S, Integrable
      (fun ω => Jsmall (b i) ω - Jsmall (a i) ω) P)
    (hWI : ∀ i ∈ S, Integrable
      (fun ω => W i ω *
        (Jsmall (b i) ω - Jsmall (a i) ω)) P) :
    Integrable (fun ω =>
      ∑ i ∈ S, W i ω * (Jsmall (b i) ω - Jsmall (a i) ω)) P ∧
    (∫ ω, ‖∑ i ∈ S,
      W i ω * (Jsmall (b i) ω - Jsmall (a i) ω)‖ ∂P) ≤
    ∑ i ∈ S, L *
      (((((b i - a i : ℝ≥0) : ℝ≥0∞) *
           X.ν (Ioo (-1 : ℝ) 0)).toReal) +
       ((b i : ℝ) - (a i : ℝ)) *
         ‖∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν‖) := by
  let M : ℕ → Ω → ℝ := fun i ω =>
    W i ω * (Jsmall (b i) ω - Jsmall (a i) ω)
  have hMI : ∀ i ∈ S, Integrable (M i) P :=
    fun i hi => hWI i hi
  have hSumI : Integrable (fun ω => ∑ i ∈ S, M i ω) P :=
    integrable_finset_sum S hMI
  have hNI : ∀ i ∈ S,
      Integrable (fun ω => L * ‖Jsmall (b i) ω - Jsmall (a i) ω‖) P :=
    fun i hi => ((hJM i hi).norm).const_mul L
  have hMajorI : Integrable (fun ω =>
      ∑ i ∈ S, L * ‖Jsmall (b i) ω - Jsmall (a i) ω‖) P :=
    integrable_finset_sum S hNI
  have hPath (ω : Ω) :
      ‖∑ i ∈ S, M i ω‖ ≤
      ∑ i ∈ S, L * ‖Jsmall (b i) ω - Jsmall (a i) ω‖ := by
    calc
      ‖∑ i ∈ S, M i ω‖ ≤ ∑ i ∈ S, ‖M i ω‖ :=
        norm_sum_le S (fun i => M i ω)
      _ = ∑ i ∈ S, ‖W i ω‖ *
            ‖Jsmall (b i) ω - Jsmall (a i) ω‖ := by
        simp only [M, norm_mul]
      _ ≤ ∑ i ∈ S, L * ‖Jsmall (b i) ω - Jsmall (a i) ω‖ := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right
          (hWBound i hi ω) (norm_nonneg _)
  have hCmp :
      (∫ ω, ‖∑ i ∈ S, M i ω‖ ∂P) ≤
      (∫ ω, ∑ i ∈ S,
        L * ‖Jsmall (b i) ω - Jsmall (a i) ω‖ ∂P) :=
    integral_mono_ae hSumI.norm hMajorI
      (Filter.Eventually.of_forall hPath)
  refine ⟨hSumI, ?_⟩
  change (∫ ω, ‖∑ i ∈ S, M i ω‖ ∂P) ≤
    ∑ i ∈ S, L *
      (((((b i - a i : ℝ≥0) : ℝ≥0∞) *
          X.ν (Ioo (-1 : ℝ) 0)).toReal) +
        ((b i : ℝ) - (a i : ℝ)) *
          ‖∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν‖)
  calc
    (∫ ω, ‖∑ i ∈ S, M i ω‖ ∂P) ≤
      (∫ ω, ∑ i ∈ S,
        L * ‖Jsmall (b i) ω - Jsmall (a i) ω‖ ∂P) := hCmp
    _ = ∑ i ∈ S, L *
        (∫ ω, ‖Jsmall (b i) ω - Jsmall (a i) ω‖ ∂P) := by
      rw [integral_finset_sum S hNI]
      simp only [integral_const_mul]
    _ ≤ ∑ i ∈ S, L *
        (((((b i - a i : ℝ≥0) : ℝ≥0∞) *
            X.ν (Ioo (-1 : ℝ) 0)).toReal) +
          ((b i : ℝ) - (a i : ℝ)) *
            ‖∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν‖) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (AvramDividend.Classical.avram_b24_original_intrinsic_smallmark_deterministic_interval_L1_linear_rate
          X hFinite Jsmall hJsource (a i) (b i)
          (hOrd i hi) (hJM i hi)) hL
