-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB78_two_grid_step_cross_time_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:03:15.717858+00:00
-- url     : https://prove2.me/submissions/ccdd444d-6de3-4224-aaea-48b4f3a5d037

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB84_two_grid_step_product_refinement_pointwise
import Theorems.Thm_AvramDividend_Classical_avram_gbB85_integral_expected_finite_step_kernel
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (n m l : ℕ) (hn : 0 < n)
    (G : ℕ → ℕ → Ω → ℝ)
    (hG : ∀ a i, StronglyMeasurable (G a i))
    (hBound : ∃ B : ℝ, 0 ≤ B ∧ ∀ a i ω, |G a i ω| ≤ B) :
    let N : ℕ := (m + 1) * (l + 1)
    let δ : ℝ := (n : ℝ) / (N : ℝ)
    let K : ℕ → ℝ → Ω → ℝ := fun k t ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      (Finset.range (k + 1)).sum (fun i =>
        if (s i : ℝ) ≤ t ∧ t < ((s i + Δ : ℝ≥0) : ℝ)
        then G k i ω else 0)
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      (∫ ω, K m t ω * K l t ω ∂P) ∂volume) =
      δ * (Finset.range N).sum (fun r =>
        ∫ ω, G m (r / (l + 1)) ω *
          G l (r / (m + 1)) ω ∂P) := by
  intro N δ K
  let F : ℕ → Ω → ℝ := fun r ω =>
    G m (r / (l + 1)) ω * G l (r / (m + 1)) ω
  have hN : 0 < N := by
    dsimp [N]
    exact Nat.mul_pos (Nat.succ_pos m) (Nat.succ_pos l)
  obtain ⟨B, hB0, hBb⟩ := hBound
  have hF : ∀ r, Integrable (F r) P := by
    intro r
    have hm := hG m (r / (l + 1))
    have hl := hG l (r / (m + 1))
    apply Integrable.of_bound (hm.mul hl).aestronglyMeasurable (B * B)
    filter_upwards with ω
    simp only [F, Pi.mul_apply, Real.norm_eq_abs, abs_mul]
    calc
      |G m (r / (l + 1)) ω| * |G l (r / (m + 1)) ω|
          ≤ B * |G l (r / (m + 1)) ω| :=
            mul_le_mul_of_nonneg_right (hBb m _ ω) (abs_nonneg _)
      _ ≤ B * B := mul_le_mul_of_nonneg_left (hBb l _ ω) hB0
  have hPoint := avram_gbB84_two_grid_step_product_refinement_pointwise
    n m l hn G
  dsimp only at hPoint
  have hKernel := avram_gbB85_integral_expected_finite_step_kernel
    P n N hn hN F hF
  dsimp only at hKernel
  have hEq :
      (∫ t in Ioo (0 : ℝ) (n : ℝ),
        (∫ ω, K m t ω * K l t ω ∂P) ∂volume) =
      (∫ t in Ioo (0 : ℝ) (n : ℝ),
        (∫ ω, (Finset.range N).sum (fun r =>
          if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
          then F r ω else 0) ∂P) ∂volume) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    apply integral_congr_ae
    filter_upwards with ω
    simpa only [K, F, N, δ] using hPoint t ht ω
  calc
    _ = (∫ t in Ioo (0 : ℝ) (n : ℝ),
        (∫ ω, (Finset.range N).sum (fun r =>
          if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
          then F r ω else 0) ∂P) ∂volume) := hEq
    _ = δ * (Finset.range N).sum (fun r =>
        ∫ ω, G m (r / (l + 1)) ω *
          G l (r / (m + 1)) ω ∂P) := by
            simpa only [F, N, δ] using hKernel
