-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_finiteactivity_jumpfree_masked_smallmark_mesh_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:06:08.074965+00:00
-- url     : https://prove2.me/submissions/e0e0d2f5-50c9-43b6-9897-0676706a2e46

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_smallmark_all_jumpfree_cells_common_conull_drift
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
    (hJsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n u ω)
        atTop (𝓝 (Jsmall u ω)))
    (S : Finset ℕ) (a b : ℕ → ℝ≥0)
    (hOrder : ∀ i ∈ S, a i ≤ b i)
    (σ : Ω → ℝ≥0) (W : ℕ → Ω → ℝ)
    (L : ℝ) (hL : 0 ≤ L)
    (hWeight : ∀ i ∈ S, ∀ ω, ‖W i ω‖ ≤ L) :
    let d : ℝ := -(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)
    ∀ᵐ ω ∂P,
      (∀ i ∈ S, ∀ u : ℝ≥0, a i < u → u ≤ b i →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) →
      ‖∑ i ∈ S, (if σ ω ≤ a i then 0 else W i ω) *
        (Jsmall (b i) ω - Jsmall (a i) ω)‖ ≤
      ∑ i ∈ S, L * ‖d * ((b i : ℝ) - (a i : ℝ))‖ := by
  let d : ℝ := -(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)
  have hSource :=
    avram_b24_original_smallmark_all_jumpfree_cells_common_conull_drift
      X hFinite Jsmall hJsource
  filter_upwards [hSource] with ω hω
  intro hNo
  have hCell (i : ℕ) (hi : i ∈ S) :
      Jsmall (b i) ω - Jsmall (a i) ω =
      d * ((b i : ℝ) - (a i : ℝ)) :=
    hω (a i) (b i) (hOrder i hi) (hNo i hi)
  calc
    ‖∑ i ∈ S, (if σ ω ≤ a i then 0 else W i ω) *
      (Jsmall (b i) ω - Jsmall (a i) ω)‖ ≤
        ∑ i ∈ S, ‖(if σ ω ≤ a i then 0 else W i ω) *
          (Jsmall (b i) ω - Jsmall (a i) ω)‖ :=
      norm_sum_le S (fun i => (if σ ω ≤ a i then 0 else W i ω) *
        (Jsmall (b i) ω - Jsmall (a i) ω))
    _ ≤ ∑ i ∈ S, L * ‖d * ((b i : ℝ) - (a i : ℝ))‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [hCell i hi, norm_mul]
      have hWi : ‖if σ ω ≤ a i then 0 else W i ω‖ ≤ L := by
        by_cases hc : σ ω ≤ a i
        · simpa [hc] using hL
        · simpa [hc] using hWeight i hi ω
      exact mul_le_mul_of_nonneg_right hWi (norm_nonneg _)
