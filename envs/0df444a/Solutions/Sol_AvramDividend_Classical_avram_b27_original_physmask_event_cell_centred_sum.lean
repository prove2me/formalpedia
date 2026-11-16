-- Prove2me | solution 1 for AvramDividend.Classical.avram_b27_original_physmask_event_cell_centred_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:21:18.962571+00:00
-- url     : https://prove2.me/submissions/d3884eb6-107d-4643-8fa9-ec79c6d28c06

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω)
    (σ : Ω → ℝ≥0) (R : ℝ≥0 → Ω → ℝ)
    (S : Finset ℕ) (a b : ℕ → ℝ≥0)
    (W : ℕ → Ω → ℝ)
    (hCellInt : ∀ i ∈ S,
      Integrable (fun ω =>
        (if σ ω ≤ a i then 0 else W i ω) *
          (R (b i) ω - R (a i) ω)) (P.restrict A))
    (hCellMean : ∀ i ∈ S,
      (∫ ω in A,
        (if σ ω ≤ a i then 0 else W i ω) *
          (R (b i) ω - R (a i) ω) ∂P) = 0) :
    (∫ ω in A, ∑ i ∈ S,
      (if σ ω ≤ a i then 0 else W i ω) *
        (R (b i) ω - R (a i) ω) ∂P) = 0 := by
  let F : ℕ → Ω → ℝ := fun i ω =>
    (if σ ω ≤ a i then 0 else W i ω) *
      (R (b i) ω - R (a i) ω)
  have hFI : ∀ i ∈ S, Integrable (F i) (P.restrict A) :=
    hCellInt
  change (∫ ω in A, ∑ i ∈ S, F i ω ∂P) = 0
  rw [integral_finset_sum S hFI]
  exact Finset.sum_eq_zero (fun i hi => hCellMean i hi)
