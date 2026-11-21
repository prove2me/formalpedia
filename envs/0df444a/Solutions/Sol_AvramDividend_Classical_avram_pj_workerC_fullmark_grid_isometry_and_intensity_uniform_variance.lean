-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_fullmark_grid_isometry_and_intensity_uniform_variance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:14:09.587683+00:00
-- url     : https://prove2.me/submissions/c5851272-193a-4a0a-a324-2306830147fb

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory Set Filter Topology
noncomputable section

/-- Uniform L2 energy bound for a stopped negative-mark compensated
physical-grid martingale, from its exact diagonal isometry and
finite original intensity budget. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : ℕ) (K B : ℝ) (hK : 0 ≤ K)
    (r : ℕ → ℝ)
    (hr : ∀ i ∈ Finset.range m, 0 ≤ r i)
    (hRate : (∑ i ∈ Finset.range m, r i) ≤ B)
    (H Z : ℕ → Ω → ℝ)
    (hHInt : ∀ i ∈ Finset.range m,
      Integrable (fun ω => (H i ω)^2) P)
    (hHBound : ∀ i ∈ Finset.range m, ∀ ω, |H i ω| ≤ K)
    (hEnergy :
      (∫ ω, ∑ i ∈ Finset.range m, (Z i ω)^2 ∂P) =
        ∑ i ∈ Finset.range m,
          r i * (∫ ω, (H i ω)^2 ∂P)) :
    (∫ ω, ∑ i ∈ Finset.range m, (Z i ω)^2 ∂P) ≤
      K^2 * B := by
  have hEach (i : ℕ) (hi : i ∈ Finset.range m) :
      (∫ ω, (H i ω)^2 ∂P) ≤ K^2 := by
    have hPoint : ∀ ω, (H i ω)^2 ≤ K^2 := by
      intro ω
      obtain ⟨hl, hu⟩ := abs_le.mp (hHBound i hi ω)
      have ha : 0 ≤ K - H i ω := by linarith
      have hb : 0 ≤ K + H i ω := by linarith
      nlinarith [mul_nonneg ha hb]
    have hMean := integral_mono_ae
      (hHInt i hi) (integrable_const (K^2))
      (Filter.Eventually.of_forall hPoint)
    simpa using hMean
  calc
    (∫ ω, ∑ i ∈ Finset.range m, (Z i ω)^2 ∂P) =
        ∑ i ∈ Finset.range m,
          r i * (∫ ω, (H i ω)^2 ∂P) := hEnergy
    _ ≤ ∑ i ∈ Finset.range m, r i * K^2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hEach i hi) (hr i hi)
    _ = (∑ i ∈ Finset.range m, r i) * K^2 := by
      rw [Finset.sum_mul]
    _ ≤ B * K^2 :=
      mul_le_mul_of_nonneg_right hRate (sq_nonneg K)
    _ = K^2 * B := by ring
