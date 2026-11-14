-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb41_original_linear_source_B_grid_equals_strict_G_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:31:12.763857+00:00
-- url     : https://prove2.me/submissions/29581cf5-dc49-4f83-903d-5bf0d9921d60

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb40_original_linear_source_compensated_jump_residual_identically_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (S : ℝ≥0)
    (hSource : ∀ t : ℝ≥0, t ≤ S → X.X t ω = (t : ℝ) * X.drift)
    (u : ℕ → ℕ → ℝ≥0)
    (hCells : ∀ n i, i ≤ n + 1 → u n i ≤ S)
    (R : ℝ≥0 → ℝ)
    (hR : ∀ t : ℝ≥0, t ≤ S →
      R t = ((t : ℝ) * X.drift - X.X t ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0))
    (coeff : ℕ → ℕ → ℝ) (B G : ℕ → ℝ)
    (hB : ∀ n, B n = G n +
      (∑ i ∈ Finset.range (n + 1),
        coeff n i * (R (u n i) - R (u n (i + 1))))) :
    ∀ n, B n = G n  := by
  have hRzero (t : ℝ≥0) (ht : t ≤ S) : R t = 0 := by
    rw [hR t ht]
    exact avram_bvb40_original_linear_source_compensated_jump_residual_identically_zero
      X ω S hSource t ht
  intro n
  rw [hB n]
  have hSum : (∑ i ∈ Finset.range (n + 1),
      coeff n i * (R (u n i) - R (u n (i + 1)))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi0 : i ≤ n + 1 :=
      Nat.le_of_lt (Finset.mem_range.mp hi)
    have hi1 : i + 1 ≤ n + 1 :=
      Nat.succ_le_of_lt (Finset.mem_range.mp hi)
    rw [hRzero (u n i) (hCells n i hi0),
      hRzero (u n (i + 1)) (hCells n (i + 1) hi1)]
    ring
  rw [hSum, add_zero]
