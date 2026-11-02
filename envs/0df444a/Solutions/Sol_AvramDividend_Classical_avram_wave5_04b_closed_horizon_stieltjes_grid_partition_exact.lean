-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_closed_horizon_stieltjes_grid_partition_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:56:19.724705+00:00
-- url     : https://prove2.me/submissions/3423c32c-c191-4f27-8722-402b188980f7

import Mathlib
import Theorems.Thm_AvramDividend_Classical_lintegral_Ioc_partition_fin

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Exact full-measure closed-horizon partition into the time-zero atom and adjacent Stieltjes cells. -/
theorem solution
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞)
    (u : ℕ → ℝ) (hu : Monotone u) (h0 : u 0 = 0) (n : ℕ) :
    (∫⁻ t in Icc (0 : ℝ) (u n), f t ∂μ) =
      (∫⁻ t in {(0 : ℝ)}, f t ∂μ) +
      ∑ i ∈ Finset.range n,
        (∫⁻ t in Ioc (u i) (u (i + 1)), f t ∂μ) := by
  have h0n : (0 : ℝ) ≤ u n := by
    have h := hu (Nat.zero_le n)
    simpa [h0] using h
  have hSet : Icc (0 : ℝ) (u n) =
      ({(0 : ℝ)} : Set ℝ) ∪ Ioc (u 0) (u n) := by
    rw [h0]
    ext r
    simp only [mem_Icc, mem_union, mem_singleton_iff, mem_Ioc]
    constructor
    · rintro ⟨hr0, hrn⟩
      rcases eq_or_lt_of_le hr0 with hrEq | hrLt
      · exact Or.inl hrEq.symm
      · exact Or.inr ⟨hrLt, hrn⟩
    · rintro (hrEq | ⟨hrLt, hrn⟩)
      · subst r
        exact ⟨le_rfl, h0n⟩
      · exact ⟨le_of_lt hrLt, hrn⟩
  have hDis : Disjoint ({(0 : ℝ)} : Set ℝ) (Ioc (u 0) (u n)) := by
    refine Set.disjoint_left.mpr ?_
    intro r hr0 hrI
    have hrEq : r = 0 := by simpa using hr0
    subst r
    have hFalse : (0 : ℝ) < 0 := by simpa [h0] using hrI.1
    exact (lt_irrefl _) hFalse
  rw [hSet, MeasureTheory.lintegral_union measurableSet_Ioc hDis,
      lintegral_Ioc_partition_fin μ f u hu n]
