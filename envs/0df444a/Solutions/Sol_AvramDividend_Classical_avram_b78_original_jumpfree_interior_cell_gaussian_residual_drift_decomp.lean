-- Prove2me | solution 1 for AvramDividend.Classical.avram_b78_original_jumpfree_interior_cell_gaussian_residual_drift_decomp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:05:08.342913+00:00
-- url     : https://prove2.me/submissions/2366c944-84e6-4c02-b774-48f824d58722

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_jb20_original_physical_random_clock_increment_split
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine original random-clock source algebra closes the pathwise unmarked Gaussian drift identity. -/
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
    (hSmall : ∀ ω i, i ∈ S → i ∉ J ω →
      Jsmall (t i ω) ω - Jsmall (s i ω) ω =
        d * (((t i ω - s i ω : ℝ≥0) : ℝ)))
    (hLarge : ∀ ω i, i ∈ S → i ∉ J ω →
      avram_p4_h_gaussian_intrinsic_large_jump_sum X (t i ω) ω =
      avram_p4_h_gaussian_intrinsic_large_jump_sum X (s i ω) ω) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0, M u ω = R u ω) ∧
      (∀ ω i, i ∈ S → i ∉ J ω →
        X.X (t i ω) ω - X.X (s i ω) ω -
          ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c =
        (M (t i ω) ω - M (s i ω) ω) +
          d * ((t i ω - s i ω : ℝ≥0) : ℝ)) := by
  classical
  obtain ⟨M, hPath, hMraw, hIncrement, hMdiff⟩ :=
    avram_jb20_original_physical_random_clock_increment_split
      X R Jsmall hRsource hJsource
  refine ⟨M, hMraw, ?_⟩
  intro ω i hi hNoMark
  have hSrc := hIncrement (s i) (t i) ω
  have hS := hSmall ω i hi hNoMark
  have hL := hLarge ω i hi hNoMark
  have hTime : ((t i ω - s i ω : ℝ≥0) : ℝ) =
      (t i ω : ℝ) - (s i ω : ℝ) :=
    NNReal.coe_sub (hOrdered ω i hi)
  rw [hL, sub_self, add_zero] at hSrc
  rw [hTime] at hS
  rw [hTime]
  linear_combination hSrc + hS
