-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b19_original_open_grid_J_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:56:46.432284+00:00
-- url     : https://prove2.me/submissions/2432b5fa-3afd-443a-8121-d632107771e6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys88_original_closed_cap_negative_mark_value_increment_nonpos
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-! Nonpositivity of the exact original marked grid-cell sum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (u : ℕ → ℕ → ℝ≥0)
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (Z : ℕ → ℝ) (σ : ℝ≥0∞) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1),
      if (u n i : ℝ≥0∞) < σ ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < C then
        (∫ z in Iio (0 : ℝ), Real.exp (-(q * (u n i : ℝ))) *
          (w (Z i + z) - w (Z i)) ∂X.ν) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0) ≤ 0 := by
  classical
  apply Finset.sum_nonpos
  intro i hi
  split_ifs with hmask
  · rcases hmask with ⟨_, hZ, hZC⟩
    have hmark : ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))),
        Real.exp (-(q * (u n i : ℝ))) *
          (w (Z i + z) - w (Z i)) ≤ 0 := by
      filter_upwards
        [MeasureTheory.ae_restrict_mem (μ := X.ν) measurableSet_Iio] with z hz
      have hinc : w (Z i + z) - w (Z i) ≤ 0 :=
        avram_bvb_phys88_original_closed_cap_negative_mark_value_increment_nonpos
          C hC w hw_cont hw0 hw_neg hw_smooth hw_grad
          (Z i) z (le_of_lt hZ) (le_of_lt hZC) hz
      exact mul_nonpos_of_nonneg_of_nonpos
        (le_of_lt (Real.exp_pos _)) hinc
    have hint : (∫ z in Iio (0 : ℝ),
        Real.exp (-(q * (u n i : ℝ))) *
          (w (Z i + z) - w (Z i)) ∂X.ν) ≤ 0 :=
      MeasureTheory.integral_nonpos_of_ae hmark
    have hstep : 0 ≤ (u n (i + 1) : ℝ) - (u n i : ℝ) := by
      apply sub_nonneg.mpr
      exact_mod_cast hmono n i (Finset.mem_range.mp hi)
    exact mul_nonpos_of_nonpos_of_nonneg hint hstep
  · exact le_refl 0
