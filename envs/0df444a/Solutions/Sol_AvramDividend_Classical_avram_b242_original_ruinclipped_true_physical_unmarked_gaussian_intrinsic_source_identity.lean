-- Prove2me | solution 1 for AvramDividend.Classical.avram_b242_original_ruinclipped_true_physical_unmarked_gaussian_intrinsic_source_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:21:04.077732+00:00
-- url     : https://prove2.me/submissions/0052a1ae-13bc-4e65-b1ab-2c4ed1208a52

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b209_original_canonical_true_unmarked_grid_gaussian_source_drift_ae
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
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
        atTop (𝓝 (R u ω)))
    (hJsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
        atTop (𝓝 (Jsmall u ω)))
    (n m : ℕ) (σ : Ω → ℝ≥0) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : Ω → ℕ → ℝ≥0 := fun ω i =>
      min ((i : ℝ≥0) * Δ) (σ ω)
    let marked : Ω → Finset ℕ := fun ω => by
      classical
      exact (Finset.range (m + 1)).filter (fun i =>
        ∃ u : ℝ≥0, v ω i < u ∧ u ≤ v ω (i + 1) ∧
          X.X u ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) u ≠ 0)
    ∀ᵐ ω ∂P, ∀ i, i ∈ Finset.range (m + 1) →
      i ∉ marked ω →
      X.X (v ω (i + 1)) ω - X.X (v ω i) ω -
        ((v ω (i + 1) - v ω i : ℝ≥0) : ℝ) * X.c =
      (R (v ω (i + 1)) ω - R (v ω i) ω) +
        (-(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)) *
          ((v ω (i + 1) - v ω i : ℝ≥0) : ℝ) := by
  classical
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let v : Ω → ℕ → ℝ≥0 := fun ω i =>
    min ((i : ℝ≥0) * Δ) (σ ω)
  let marked : Ω → Finset ℕ := fun ω =>
    (Finset.range (m + 1)).filter (fun i =>
      ∃ u : ℝ≥0, v ω i < u ∧ u ≤ v ω (i + 1) ∧
        X.X u ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) u ≠ 0)
  have hOrdered (ω : Ω) (i : ℕ) (hi : i ∈ Finset.range (m + 1)) :
      v ω i ≤ v ω (i + 1) := by
    dsimp [v]
    gcongr <;> omega
  have hCanon (ω : Ω) (i : ℕ) :
      i ∈ marked ω ↔ i ∈ Finset.range (m + 1) ∧
        ∃ u : ℝ≥0, v ω i < u ∧ u ≤ v ω (i + 1) ∧
          X.X u ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) u ≠ 0 := by
    simp only [marked, Finset.mem_filter]
  exact avram_b209_original_canonical_true_unmarked_grid_gaussian_source_drift_ae
    X hFinite R Jsmall hRsource hJsource
    (Finset.range (m + 1))
    (fun i ω => v ω i) (fun i ω => v ω (i + 1))
    hOrdered marked hCanon
