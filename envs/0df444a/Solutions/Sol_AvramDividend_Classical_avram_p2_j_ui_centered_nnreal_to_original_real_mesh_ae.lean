-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_centered_nnreal_to_original_real_mesh_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:06:31.619771+00:00
-- url     : https://prove2.me/submissions/76bb9656-bf41-40db-a306-5a7fad646a78

import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_uniform_nnreal_real_mesh_identification

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal BigOperators

/-! Source-exact conversion of centered càdlàg NNReal grid limits to P2-J's real-grid convention. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (g : ℝ → ℝ) (Z : Ω → ℝ)
    (hcenter : ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range (n + 1),
        g ((X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω - X 0 ω) -
           (X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω - X 0 ω)))
      atTop (nhds (Z ω))) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range (n + 1),
        g (X ((↑(i + 1) : ℝ≥0) * Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω -
           X ((i : ℝ≥0) * Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω))
      atTop (nhds (Z ω)) := by
  filter_upwards [hcenter] with ω hω
  have heq (n : ℕ) :
      (∑ i ∈ Finset.range (n + 1),
        g (X ((↑(i + 1) : ℝ≥0) * Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω -
           X ((i : ℝ≥0) * Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω)) =
      (∑ i ∈ Finset.range (n + 1),
        g ((X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω - X 0 ω) -
           (X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω - X 0 ω))) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp_rw [avram_p2_j_ui_uniform_nnreal_real_mesh_identification T n]
    congr 1
    ring
  have hfun :
      (fun n : ℕ => ∑ i ∈ Finset.range (n + 1),
        g (X ((↑(i + 1) : ℝ≥0) * Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω -
           X ((i : ℝ≥0) * Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω)) =
      (fun n : ℕ => ∑ i ∈ Finset.range (n + 1),
        g ((X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω - X 0 ω) -
           (X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω - X 0 ω))) := by
    funext n
    exact heq n
  rw [hfun]
  exact hω
