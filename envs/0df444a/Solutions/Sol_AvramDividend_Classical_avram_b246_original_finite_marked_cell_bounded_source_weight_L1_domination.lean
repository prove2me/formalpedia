-- Prove2me | solution 1 for AvramDividend.Classical.avram_b246_original_finite_marked_cell_bounded_source_weight_L1_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:26:38.044702+00:00
-- url     : https://prove2.me/submissions/a842a0d7-c659-4172-873b-b0c4ffc0fab3

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (marked : Ω → Finset ℕ)
    (hCount : Integrable (fun ω => ((marked ω).card : ℝ)) P)
    (W : Ω → ℕ → ℝ)
    (hMeas : AEStronglyMeasurable
      (fun ω => ∑ i ∈ marked ω, W ω i) P)
    (L : ℝ) (hL : 0 ≤ L)
    (hBound : ∀ ω i, i ∈ marked ω → ‖W ω i‖ ≤ L) :
    Integrable (fun ω => ∑ i ∈ marked ω, W ω i) P ∧
    ∀ ω, ‖∑ i ∈ marked ω, W ω i‖ ≤
      L * ((marked ω).card : ℝ) := by
  have hBoundTotal (ω : Ω) :
      ‖∑ i ∈ marked ω, W ω i‖ ≤
        L * ((marked ω).card : ℝ) := by
    calc
      ‖∑ i ∈ marked ω, W ω i‖ ≤
          ∑ i ∈ marked ω, ‖W ω i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ marked ω, L := by
        apply Finset.sum_le_sum
        intro i hi
        exact hBound ω i hi
      _ = L * ((marked ω).card : ℝ) := by
        simp [mul_comm]
  have hMaj : Integrable
      (fun ω => L * ((marked ω).card : ℝ)) P :=
    hCount.const_mul L
  constructor
  · exact hMaj.mono' hMeas (Filter.Eventually.of_forall hBoundTotal)
  · exact hBoundTotal
