-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a141_original_gaussian_random_crossing_uniform_positive_cell_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:03:12.593068+00:00
-- url     : https://prove2.me/submissions/557da47c-cf6f-4bd0-b178-e390b0fb61fc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a98_original_gaussian_true_crossing_positive_cell_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- At most one genuinely stop-straddling Gaussian cell makes every uniform vanishing positive pathwise crossing budget vanish without a mesh-count factor. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (f : ℕ → ℕ → Ω → ℝ) (B : ℕ → Ω → ℝ)
    (hB : ∀ m ω, 0 ≤ B m ω)
    (hBound : ∀ (m : ℕ) (ω : Ω) (i : ℕ), i < m →
      (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) < ρ ω →
      ρ ω ≤ ((Nat.succ i : ℕ) : ℝ≥0) *
        ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) →
      max (f m i ω) 0 ≤ B m ω)
    (hBae : ∀ᵐ ω ∂P, Tendsto (fun m => B m ω)
      atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂P, Tendsto (fun m =>
      ∑ i ∈ Finset.range m,
        if (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) < ρ ω ∧
          ρ ω ≤ ((Nat.succ i : ℕ) : ℝ≥0) *
            ((n : ℝ≥0) / ((m : ℝ≥0) + 1))
        then max (f m i ω) 0 else 0)
      atTop (𝓝 (0 : ℝ)) := by
  filter_upwards [hBae] with ω hω
  have hUpper (m : ℕ) :
      (∑ i ∈ Finset.range m,
        if (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) < ρ ω ∧
          ρ ω ≤ ((Nat.succ i : ℕ) : ℝ≥0) *
            ((n : ℝ≥0) / ((m : ℝ≥0) + 1))
        then max (f m i ω) 0 else 0) ≤ B m ω :=
    avram_ga_a98_original_gaussian_true_crossing_positive_cell_budget
      n m (ρ ω) (fun i => f m i ω) (B m ω) (hB m ω)
      (fun i hi hs hc => hBound m ω i hi hs hc)
  have hLower (m : ℕ) :
      0 ≤ (∑ i ∈ Finset.range m,
        if (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) < ρ ω ∧
          ρ ω ≤ ((Nat.succ i : ℕ) : ℝ≥0) *
            ((n : ℝ≥0) / ((m : ℝ≥0) + 1))
        then max (f m i ω) 0 else 0) := by
    apply Finset.sum_nonneg
    intro i hi
    split_ifs <;> [exact le_max_right _ 0; exact le_refl 0]
  exact squeeze_zero hLower hUpper hω
