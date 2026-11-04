-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_finite_grid_sum_from_selected_cells
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:50:05.370207+00:00
-- url     : https://prove2.me/submissions/3a14565a-8463-4d3b-b7ef-857f39bb4517

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Defs.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_finite_continuous_test_sum_tendsto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology AvramDividend.Classical

/-- Eventually all non-selected grid weights vanish, so a full finite
mesh sum converges to its selected genuine jump sum. -/
theorem solution
    {α : Type*} (s : Finset α)
    (grid : ℕ → Finset ℕ)
    (idx : α → ℕ → ℕ)
    (mark : ℕ → ℕ → ℝ) (jump : α → ℝ)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hinj : ∀ᶠ n : ℕ in atTop,
      Set.InjOn (fun u => idx u n) (s : Set α))
    (hinside : ∀ n, ∀ u ∈ s, idx u n ∈ grid n)
    (hzero : ∀ᶠ n : ℕ in atTop,
      ∀ j ∈ grid n, j ∉ s.image (fun u => idx u n) →
        f (mark n j) = 0)
    (hmark : ∀ u ∈ s,
      Tendsto (fun n => mark n (idx u n)) atTop (𝓝 (jump u))) :
    Tendsto (fun n => ∑ j ∈ grid n, f (mark n j))
      atTop (𝓝 (∑ u ∈ s, f (jump u))) := by
  classical
  have hselected :=
    avram_p2_a_zero_rate_finite_continuous_test_sum_tendsto
      s (fun u n => mark n (idx u n)) jump f hf hmark
  have heq : ∀ᶠ n : ℕ in atTop,
      (∑ u ∈ s, f (mark n (idx u n))) =
      (∑ j ∈ grid n, f (mark n j)) := by
    filter_upwards [hinj, hzero] with n hn hz
    have hsub : s.image (fun u => idx u n) ⊆ grid n := by
      intro j hj
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hj
      exact hinside n u hu
    have hsum : (∑ j ∈ s.image (fun u => idx u n), f (mark n j)) =
        (∑ j ∈ grid n, f (mark n j)) :=
      Finset.sum_subset hsub (fun j hjgrid hjnot => hz j hjgrid hjnot)
    rw [Finset.sum_image (fun u hu v hv heq => hn hu hv heq)] at hsum
    exact hsum
  exact hselected.congr' heq
