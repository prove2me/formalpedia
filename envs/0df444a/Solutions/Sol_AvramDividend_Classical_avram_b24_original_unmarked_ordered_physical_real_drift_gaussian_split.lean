-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_unmarked_ordered_physical_real_drift_gaussian_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:35:40.217346+00:00
-- url     : https://prove2.me/submissions/1e3ef111-24a4-4a33-a230-475e085f380b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_b213_original_global_intrinsic_martingales_and_canonical_unmarked_grid_split
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)

    (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (hOrdered : ∀ ω i, i ∈ S → s i ω ≤ t i ω)
    (J : Ω → Finset ℕ)
    (hJcanon : ∀ ω i, i ∈ J ω ↔ i ∈ S ∧
      ∃ u : ℝ≥0, s i ω < u ∧ u ≤ t i ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
 :
    ∃ (R Jsmall M : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
          atTop (𝓝 (R u ω))) ∧
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
          atTop (𝓝 (Jsmall u ω))) ∧
      (∀ u : ℝ≥0, Integrable (R u) P) ∧
      (∀ u : ℝ≥0, Integrable (Jsmall u) P) ∧
      (∀ a b : ℝ≥0, a ≤ b →
        ∀ᵐ ω ∂P, condExp (𝓕.rightCont a) P (R b) ω = R a ω) ∧
      (∀ a b : ℝ≥0, a ≤ b →
        ∀ᵐ ω ∂P, condExp (𝓕.rightCont a) P (Jsmall b) ω = Jsmall a ω) ∧
      (∀ u ω, X.X u ω = (u : ℝ) * X.c + M u ω + Jsmall u ω +
        avram_p4_h_gaussian_intrinsic_large_jump_sum X u ω) ∧
      (∀ᵐ ω ∂P, ∀ i, i ∈ S → i ∉ J ω →
        X.X (t i ω) ω - X.X (s i ω) ω -
          ((t i ω : ℝ) - (s i ω : ℝ)) * X.c =
        (R (t i ω) ω - R (s i ω) ω) +
          (-(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)) *
            ((t i ω : ℝ) - (s i ω : ℝ))):= by
  obtain ⟨R, Jsmall, M, hR, hJ, hRI, hJI, hRC, hJC, hD, hSplit⟩ :=
    avram_b213_original_global_intrinsic_martingales_and_canonical_unmarked_grid_split
      X hX hFinite S s t hOrdered J hJcanon
  refine ⟨R, Jsmall, M, hR, hJ, hRI, hJI, hRC, hJC, hD, ?_⟩
  filter_upwards [hSplit] with ω hs
  intro i hi hno
  have hEq := hs i hi hno
  have hCo : (((t i ω - s i ω : ℝ≥0) : ℝ)) =
      (t i ω : ℝ) - (s i ω : ℝ) :=
    NNReal.coe_sub (hOrdered ω i hi)
  simpa only [hCo] using hEq
