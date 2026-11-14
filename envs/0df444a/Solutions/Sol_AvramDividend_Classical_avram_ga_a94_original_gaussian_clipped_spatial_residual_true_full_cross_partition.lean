-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a94_original_gaussian_clipped_spatial_residual_true_full_cross_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:25:40.851739+00:00
-- url     : https://prove2.me/submissions/06ceac68-eb3f-4d70-8f96-f43b360e3064

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a71_original_gaussian_fullcell_clipped_spatial_endpoint_eq_source
import Theorems.Thm_AvramDividend_Classical_avram_ga_a89_original_poststop_clipped_spatial_residual_cell_zero
import Theorems.Thm_AvramDividend_Classical_avram_ga_a72_original_gaussian_crossing_cell_clipped_endpoint_eq_stopped_source
import Theorems.Thm_AvramDividend_Classical_avram_ga_a93_original_gaussian_stopped_full_cross_post_partition_finite_grid
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- The original clipped Gaussian spatial HJB residual is exactly the sum of physically full pre-stop contributions and true stopped crossing contributions, with all other source cells zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (ω : Ω) (n m : ℕ) (ρ : ℝ≥0) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let v : ℕ → ℝ≥0 := fun i => min (s i) ρ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t =>
      x + X.X t ω - rightLimit D t ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
    let H : ℕ → ℝ := fun i =>
      E (s i) * (deriv w (Y (s i)) * Z i +
        (iteratedDeriv 2 w (Y (s i)) / 2) *
          (Z i^2 - (Δ : ℝ) * X.σ^2)) +
        (Δ : ℝ) * E (s i) * X.generator w (Y (s i))
    let U : ℕ → ℝ := fun i =>
      E (v (i + 1)) *
        (w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω) -
          w (Y (v i))) -
      (if s i < ρ then H i else 0)
    let F : ℕ → ℝ := fun i =>
      E (s i + Δ) * (w (Y (s i) + R i) - w (Y (s i))) - H i
    let C : ℕ → ℝ := fun i =>
      E ρ * (w (Y (s i) + (X.X ρ ω - X.X (s i) ω)) -
        w (Y (s i))) - H i
    (∑ i ∈ Finset.range m, U i) =
      (∑ i ∈ Finset.range m,
        if s i < ρ ∧ s i + Δ ≤ ρ then F i else 0) +
      (∑ i ∈ Finset.range m,
        if s i < ρ ∧ ρ < s i + Δ then C i else 0) := by
  classical
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
  let v : ℕ → ℝ≥0 := fun i => min (s i) ρ
  let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
  let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
  let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
  let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
  let H : ℕ → ℝ := fun i =>
    E (s i) * (deriv w (Y (s i)) * Z i +
      (iteratedDeriv 2 w (Y (s i)) / 2) * (Z i^2 - (Δ : ℝ) * X.σ^2)) +
      (Δ : ℝ) * E (s i) * X.generator w (Y (s i))
  let U : ℕ → ℝ := fun i => E (v (i + 1)) *
    (w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω) - w (Y (v i))) -
    (if s i < ρ then H i else 0)
  let F : ℕ → ℝ := fun i =>
    E (s i + Δ) * (w (Y (s i) + R i) - w (Y (s i))) - H i
  let C : ℕ → ℝ := fun i => E ρ *
    (w (Y (s i) + (X.X ρ ω - X.X (s i) ω)) - w (Y (s i))) - H i
  change (∑ i ∈ Finset.range m, U i) =
      (∑ i ∈ Finset.range m,
        if s i < ρ ∧ s i + Δ ≤ ρ then F i else 0) +
      (∑ i ∈ Finset.range m,
        if s i < ρ ∧ ρ < s i + Δ then C i else 0)
  apply avram_ga_a93_original_gaussian_stopped_full_cross_post_partition_finite_grid
    (Finset.range m) s Δ ρ U F C
  · intro i hs hf
    obtain ⟨hv0,hv1,_⟩ :=
      avram_ga_a71_original_gaussian_fullcell_clipped_spatial_endpoint_eq_source
        X x D ω n m i ρ hf
    change U i = F i; dsimp only [U, F]; simp only [if_pos hs]
    change v i = s i at hv0; change v (i + 1) = s i + Δ at hv1
    rw [hv0, hv1]
    have hSpatial : x + X.X (s i + Δ) ω - rightLimit D (s i) ω =
        Y (s i) + R i := by
      dsimp [Y, R]; ring
    rw [hSpatial]
  · intro i hs hc
    obtain ⟨hv0,hv1,_⟩ :=
      avram_ga_a72_original_gaussian_crossing_cell_clipped_endpoint_eq_stopped_source
        X x D ω n m i ρ hs hc.le
    change U i = C i; dsimp only [U, C]
    change v i = s i at hv0; change v (i + 1) = ρ at hv1
    rw [hv0, hv1]; simp only [if_pos hs]
    have hSpatial : x + X.X ρ ω - rightLimit D (s i) ω =
        Y (s i) + (X.X ρ ω - X.X (s i) ω) := by
      dsimp [Y]; ring
    rw [hSpatial]
  · intro i hp
    have hv0 : v i = ρ := by
      change min (s i) ρ = ρ
      exact min_eq_right hp
    have hsNext : s (i + 1) = s i + Δ := by
      dsimp [s]; push_cast; ring
    have hv1 : v (i + 1) = ρ := by
      change min (s (i + 1)) ρ = ρ
      apply min_eq_right; rw [hsNext]
      exact le_trans hp (le_add_of_nonneg_right (zero_le))
    have hNot : ¬ s i < ρ := not_lt.mpr hp
    change U i = 0; dsimp only [U]
    rw [hv0, hv1]
    simp only [if_neg hNot, sub_zero]; dsimp [Y]; ring
