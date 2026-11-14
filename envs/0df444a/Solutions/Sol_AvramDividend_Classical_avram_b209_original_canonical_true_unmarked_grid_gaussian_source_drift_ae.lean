-- Prove2me | solution 1 for AvramDividend.Classical.avram_b209_original_canonical_true_unmarked_grid_gaussian_source_drift_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:02:09.68448+00:00
-- url     : https://prove2.me/submissions/54cb0acf-cce3-4825-b026-d616da4a4418

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b159_original_true_unmarked_cell_ae_gaussian_source_drift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- True unmarked source grid cells obey the intrinsic Gaussian residual and negative compensator drift a.e. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsrc : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
        atTop (𝓝 (R u ω)))
    (hJsrc : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
        atTop (𝓝 (Jsmall u ω)))
    (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (hOrdered : ∀ ω i, i ∈ S → s i ω ≤ t i ω)
    (J : Ω → Finset ℕ)
    (hJcanon : ∀ ω i, i ∈ J ω ↔ i ∈ S ∧
      ∃ u : ℝ≥0, s i ω < u ∧ u ≤ t i ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) :
    ∀ᵐ ω ∂P, ∀ i, i ∈ S → i ∉ J ω →
      X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c =
      (R (t i ω) ω - R (s i ω) ω) +
        (-(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)) *
          ((t i ω - s i ω : ℝ≥0) : ℝ) := by
  classical
  apply (ae_all_iff).2
  intro i
  by_cases hi : i ∈ S
  · have hUnmarked (ω : Ω) (hUn : ¬ i ∈ J ω) (u : ℝ≥0)
        (hsu : s i ω < u) (hut : u ≤ t i ω) :
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 := by
      by_contra hne
      exact hUn ((hJcanon ω i).2 ⟨hi, ⟨u, hsu, hut, hne⟩⟩)
    have hCell :=
      avram_b159_original_true_unmarked_cell_ae_gaussian_source_drift
        X hFinite R Jsmall hRsrc hJsrc (s i) (t i)
        (fun ω => hOrdered ω i hi) (fun ω => i ∈ J ω)
        hUnmarked
    filter_upwards [hCell] with ω hω
    intro _ hUn
    have hSource := hω hUn
    have hTime : ((t i ω - s i ω : ℝ≥0) : ℝ) =
        (t i ω : ℝ) - (s i ω : ℝ) :=
      NNReal.coe_sub (hOrdered ω i hi)
    rw [hTime]
    nlinarith [hSource]
  · exact Filter.Eventually.of_forall (fun ω hiS => (hi hiS).elim)