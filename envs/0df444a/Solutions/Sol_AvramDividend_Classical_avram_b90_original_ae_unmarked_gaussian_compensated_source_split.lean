-- Prove2me | solution 1 for AvramDividend.Classical.avram_b90_original_ae_unmarked_gaussian_compensated_source_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:55:41.921256+00:00
-- url     : https://prove2.me/submissions/0b308bb5-52c0-4773-a55a-999435c6a0ce

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_jb19_original_gaussian_residual_totalise_source_path
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original Gaussian component accounts for all unmarked-cell increments after compensation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω)))
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (𝓝 (Jsmall t ω)))
    (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (J : Ω → Finset ℕ) (d : ℝ)
    (hOrdered : ∀ ω i, i ∈ S → s i ω ≤ t i ω)
    (hSmall : ∀ᵐ ω ∂P, ∀ i, i ∈ S → i ∉ J ω →
      Jsmall (t i ω) ω - Jsmall (s i ω) ω =
        d * (((t i ω - s i ω : ℝ≥0) : ℝ)))
    (hLarge : ∀ᵐ ω ∂P, ∀ i, i ∈ S → i ∉ J ω →
      avram_p4_h_gaussian_intrinsic_large_jump_sum X (t i ω) ω =
      avram_p4_h_gaussian_intrinsic_large_jump_sum X (s i ω) ω) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0, M u ω = R u ω) ∧
      (∀ᵐ ω ∂P, ∀ i, i ∈ S → i ∉ J ω →
        X.X (t i ω) ω - X.X (s i ω) ω -
          ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c =
        (M (t i ω) ω - M (s i ω) ω) +
          d * ((t i ω - s i ω : ℝ≥0) : ℝ)) := by
  obtain ⟨M, hPath, hM⟩ :=
    avram_jb19_original_gaussian_residual_totalise_source_path
      X R Jsmall hRsource hJsource
  refine ⟨M, hM, ?_⟩
  filter_upwards [hSmall, hLarge] with ω hSω hLω
  intro i hi hnot
  have hS := hSω i hi hnot
  have hL := hLω i hi hnot
  have hSub : ((t i ω - s i ω : ℝ≥0) : ℝ) =
      (t i ω : ℝ) - (s i ω : ℝ) :=
    NNReal.coe_sub (hOrdered ω i hi)
  calc
    X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c =
      (M (t i ω) ω - M (s i ω) ω) +
        (Jsmall (t i ω) ω - Jsmall (s i ω) ω) +
        (avram_p4_h_gaussian_intrinsic_large_jump_sum X (t i ω) ω -
          avram_p4_h_gaussian_intrinsic_large_jump_sum X (s i ω) ω) := by
      rw [hPath (t i ω) ω, hPath (s i ω) ω, hSub]
      ring
    _ = (M (t i ω) ω - M (s i ω) ω) +
        d * ((t i ω - s i ω : ℝ≥0) : ℝ) := by
      rw [hS, hL]
      ring
