-- Prove2me | solution 1 for AvramDividend.Classical.finite_grid_partition_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:30:22.729787+00:00
-- url     : https://prove2.me/submissions/02108302-9400-4d69-9d44-a039c739d3d7

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0)
    (hgrid : ∀ ω, τ ω ∈ grid)
    (hfib : ∀ s ∈ grid, MeasurableSet {ω : Ω | τ ω = s})
    (f : ℝ≥0 → Ω → ℝ)
    (hint : ∀ s ∈ grid, Integrable (f s) P)
    (c : ℝ)
    (heach : ∀ s ∈ grid,
      ∫ ω in {ω : Ω | τ ω = s}, f s ω ∂P =
        (P {ω : Ω | τ ω = s}).toReal * c) :
    ∫ ω, f (τ ω) ω ∂P = c := by
  classical
  let B : ℝ≥0 → Set Ω := fun s => {ω | τ ω = s}
  have hd : PairwiseDisjoint (↑grid : Set ℝ≥0) B := by
    intro s hs t ht hst
    apply Set.disjoint_left.mpr
    intro ω hws hwt
    exact hst (hws.symm.trans hwt)
  have hcover : (⋃ s ∈ grid, B s) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨τ ω, hgrid ω, rfl⟩
  have hmeas : ∀ s ∈ grid, MeasurableSet (B s) := by
    intro s hs
    exact hfib s hs
  have hmass : (∑ s ∈ grid, P (B s)) = 1 := by
    calc
      (∑ s ∈ grid, P (B s)) =
          P (⋃ s ∈ grid, B s) :=
        (measure_biUnion_finset hd hmeas).symm
      _ = 1 := by rw [hcover]; simp
  have hfinite : ∀ s ∈ grid, P (B s) ≠ ⊤ := by
    intro s hs
    exact measure_ne_top P (B s)
  have hmassReal : (∑ s ∈ grid, (P (B s)).toReal) = 1 := by
    rw [← ENNReal.toReal_sum hfinite, hmass]
    norm_num
  have hintPart : ∀ s ∈ grid, Integrable ((B s).indicator (f s)) P := by
    intro s hs
    exact (hint s hs).indicator (hfib s hs)
  have hpart (ω : Ω) :
      f (τ ω) ω =
        ∑ s ∈ grid, (B s).indicator (f s) ω := by
    simp [B, Set.indicator, hgrid ω, eq_comm]
  calc
    (∫ ω, f (τ ω) ω ∂P) =
        ∫ ω, ∑ s ∈ grid, (B s).indicator (f s) ω ∂P := by
      congr 1
      funext ω
      exact hpart ω
    _ = ∑ s ∈ grid, (∫ ω, (B s).indicator (f s) ω ∂P) := by
      exact integral_finset_sum grid hintPart
    _ = ∑ s ∈ grid, (P (B s)).toReal * c := by
      apply Finset.sum_congr rfl
      intro s hs
      simpa only [B, integral_indicator (hfib s hs)] using heach s hs
    _ = c := by rw [← Finset.sum_mul, hmassReal, one_mul]
