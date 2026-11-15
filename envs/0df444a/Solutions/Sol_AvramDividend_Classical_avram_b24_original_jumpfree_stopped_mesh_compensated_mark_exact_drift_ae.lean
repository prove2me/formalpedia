-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_jumpfree_stopped_mesh_compensated_mark_exact_drift_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:03:43.619211+00:00
-- url     : https://prove2.me/submissions/d776bade-4ced-41b6-85af-f55444eec675

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
    (hOrdered : ∀ i ∈ S, a i ≤ b i)
    (σ : Ω → ℝ≥0) (W : ℕ → Ω → ℝ) :
    ∀ᵐ ω ∂P,
      (∀ i ∈ S, ∀ u : ℝ≥0, a i < u → u ≤ b i →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) →
      (∑ i ∈ S, (if σ ω ≤ a i then 0 else W i ω) *
        (Jsmall (b i) ω - Jsmall (a i) ω)) =
      -(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) *
        (∑ i ∈ S, (if σ ω ≤ a i then 0 else W i ω) *
          ((b i : ℝ) - (a i : ℝ))) := by
  have hSource :=
    avram_b24_original_smallmark_all_jumpfree_cells_common_conull_drift
      X hFinite Jsmall hJsource
  filter_upwards [hSource] with ω hω
  intro hNoJump
  have hCell (i : ℕ) (hi : i ∈ S) :
      Jsmall (b i) ω - Jsmall (a i) ω =
        -(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) *
          ((b i : ℝ) - (a i : ℝ)) :=
    hω (a i) (b i) (hOrdered i hi) (hNoJump i hi)
  calc
    (∑ i ∈ S, (if σ ω ≤ a i then 0 else W i ω) *
      (Jsmall (b i) ω - Jsmall (a i) ω)) =
        ∑ i ∈ S, (if σ ω ≤ a i then 0 else W i ω) *
          (-(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) *
            ((b i : ℝ) - (a i : ℝ))) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hCell i hi]
    _ = -(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) *
        (∑ i ∈ S, (if σ ω ≤ a i then 0 else W i ω) *
          ((b i : ℝ) - (a i : ℝ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
