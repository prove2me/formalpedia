-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_rightCont_physical_Gaussian_MDS_L2_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T00:48:41.388121+00:00
-- url     : https://prove2.me/submissions/0344ed04-b544-4b79-ad87-e155cfb2529c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_rightCont_physical_time_MDS_to_natural_grid_filtration
import Theorems.Thm_AvramDividend_Classical_avram_ga_predictable_centered_quadratic_mesh_L2_diagonal_bound
open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (Δ : ℝ≥0) (U : ℕ → Ω → ℝ)
    (hLp : ∀ i, MemLp (U i) 2 P)
    (hAdapt : ∀ (i : ℕ), StronglyMeasurable[
      𝓕.rightCont (((i + 1 : ℕ) : ℝ≥0) * Δ)] (U i))
    (hCenter : ∀ (i : ℕ),
      P[U i | 𝓕.rightCont ((i : ℝ≥0) * Δ)] =ᵐ[P] (fun _ => (0 : ℝ)))
    (n : ℕ) (K : ℝ)
    (hVar : ∀ i < n,
      (∫ ω, (U i ω) ^ 2 ∂P) ≤ K * (Δ : ℝ) ^ 2) :
    (∫ ω, (∑ i ∈ Finset.range n, U i ω) ^ 2 ∂P) ≤
      (n : ℝ) * (K * (Δ : ℝ) ^ 2) := by
  let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
  have hs : Monotone s := by
    intro i j hij
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (show (0 : ℝ≥0) ≤ Δ from zero_le)
  obtain ⟨𝓖, h𝓖, hA, hC⟩ :=
    avram_ga_rightCont_physical_time_MDS_to_natural_grid_filtration
      P 𝓕 s hs U (by simpa [s] using hAdapt) (by simpa [s] using hCenter)
  exact avram_ga_predictable_centered_quadratic_mesh_L2_diagonal_bound
    P 𝓖 U hLp hA hC n K (Δ : ℝ) hVar
