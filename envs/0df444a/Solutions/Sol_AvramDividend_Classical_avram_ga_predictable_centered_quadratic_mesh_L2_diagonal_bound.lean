-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_predictable_centered_quadratic_mesh_L2_diagonal_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T00:09:21.110167+00:00
-- url     : https://prove2.me/submissions/e644d413-5a09-4e4b-8f3f-2146a0733d4f

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_Martingale_integral_sq_sum_eq_sum_integral_sq
open MeasureTheory Filter
noncomputable section

theorem solution
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsFiniteMeasure P]
    (𝓕 : Filtration ℕ mΩ) (H : ℕ → Ω → ℝ)
    (hLp : ∀ i, MemLp (H i) 2 P)
    (hAdapt : ∀ i, StronglyMeasurable[𝓕 (i + 1)] (H i))
    (hCenter : ∀ i, P[H i | 𝓕 i] =ᵐ[P] 0)
    (n : ℕ) (K Δ : ℝ)
    (hVar : ∀ i < n, (∫ ω, (H i ω) ^ 2 ∂P) ≤ K * Δ ^ 2) :
    (∫ ω, (∑ i ∈ Finset.range n, H i ω) ^ 2 ∂P) ≤
      (n : ℝ) * (K * Δ ^ 2) := by
  rw [Martingale.integral_sq_sum_eq_sum_integral_sq
    P 𝓕 H hLp hAdapt hCenter n]
  calc
    (∑ i ∈ Finset.range n, ∫ ω, (H i ω) ^ 2 ∂P) ≤
        ∑ i ∈ Finset.range n, K * Δ ^ 2 := by
          exact Finset.sum_le_sum (fun i hi =>
            hVar i (Finset.mem_range.mp hi))
    _ = (n : ℝ) * (K * Δ ^ 2) := by
          simp [nsmul_eq_mul]
