-- Prove2me | solution 1 for AvramDividend.Classical.avram_b87_original_true_negative_markfree_intrinsic_gaussian_drift_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:13:37.323138+00:00
-- url     : https://prove2.me/submissions/2f02849b-826a-4463-9ded-e13e30f6276a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_b78_original_jumpfree_interior_cell_gaussian_residual_drift_decomp
import Theorems.Thm_AvramDividend_Classical_avram_b86_original_true_jumpfree_selected_cells_both_negative_channels
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Original finite activity jumpfree mesh cell source increments have their intrinsic same-filtration Gaussian residual and exact ν compensation drift. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun n => avram_p4_h_gaussian_intrinsic_truncated_residual X n u ω)
        atTop (𝓝 (R u ω)))
    (hJsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun n => avram_p4_h_gaussian_intrinsic_small_band_compensated X n u ω)
        atTop (𝓝 (Jsmall u ω)))
    (hJtotal : ∀ ω u, Tendsto
      (fun n => avram_p4_h_gaussian_intrinsic_small_band_compensated X n u ω)
      atTop (𝓝 (Jsmall u ω)))
    (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0) (J : Ω → Finset ℕ)
    (hOrdered : ∀ ω i, i ∈ S → s i ω ≤ t i ω)
    (hNoJump : ∀ ω i, i ∈ S → i ∉ J ω →
      ∀ u : ℝ≥0, s i ω < u → u ≤ t i ω →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0, M u ω = R u ω) ∧
      (∀ ω i, i ∈ S → i ∉ J ω →
        X.X (t i ω) ω - X.X (s i ω) ω -
          ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c =
        (M (t i ω) ω - M (s i ω) ω) +
          (-(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)) *
            ((t i ω - s i ω : ℝ≥0) : ℝ)) := by
  have hBoth :=
    avram_b86_original_true_jumpfree_selected_cells_both_negative_channels
      X hFinite Jsmall hJtotal S s t J hOrdered hNoJump
  have hSmall (ω : Ω) (i : ℕ) (hi : i ∈ S) (hNot : i ∉ J ω) :
      Jsmall (t i ω) ω - Jsmall (s i ω) ω =
        (-(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)) *
          ((t i ω - s i ω : ℝ≥0) : ℝ) := by
    have h := (hBoth ω i hi hNot).1
    rw [NNReal.coe_sub (hOrdered ω i hi)]
    exact h
  have hLarge (ω : Ω) (i : ℕ) (hi : i ∈ S) (hNot : i ∉ J ω) :
      avram_p4_h_gaussian_intrinsic_large_jump_sum X (t i ω) ω =
        avram_p4_h_gaussian_intrinsic_large_jump_sum X (s i ω) ω :=
    (hBoth ω i hi hNot).2
  exact avram_b78_original_jumpfree_interior_cell_gaussian_residual_drift_decomp
    X R Jsmall hRsource hJsource S s t J
    (-(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν))
    hOrdered hSmall hLarge
