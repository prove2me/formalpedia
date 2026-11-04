-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_full_grid_compact_test_jump_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:59:49.361859+00:00
-- url     : https://prove2.me/submissions/8791c803-b9a8-42e0-82b3-56f2c527f135

import Mathlib.Topology.Order.LeftRightLim
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_large_cells_cross_finite_true_jumps
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_finite_grid_sum_from_selected_cells
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology AvramDividend.Classical
open scoped NNReal

/-- The full original càdlàg source-grid compact-test sum converges to the
finite genuine jump sum whenever selected jump cells are uniquely located. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0)
    (a b : ℕ → ℕ → ℝ≥0) (w : ℕ → ℝ≥0)
    (haT : ∀ n i, a n i ≤ T)
    (hab : ∀ n i, a n i ≤ b n i)
    (hbw : ∀ n i, b n i ≤ a n i + w n)
    (hw : Tendsto w atTop (𝓝 (0 : ℝ≥0)))
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t)
    (ρ : ℝ) (hρ : 0 < ρ)
    (F : Finset ℝ≥0)
    (hF : ∀ t ∈ Icc (0 : ℝ≥0) T,
      ρ ≤ |Y t - Function.leftLim Y t| → t ∈ F)
    (grid : ℕ → Finset ℕ) (idx : ℝ≥0 → ℕ → ℕ)
    (hinside : ∀ n, ∀ t ∈ F, idx t n ∈ grid n)
    (hinj : ∀ᶠ n : ℕ in atTop,
      Set.InjOn (fun t => idx t n) (F : Set ℝ≥0))
    (hunique : ∀ n i, ∀ t ∈ F,
      a n i < t ∧ t ≤ b n i → i = idx t n)
    (hselected : ∀ t ∈ F,
      Tendsto (fun n => Y (b n (idx t n)) - Y (a n (idx t n)))
        atTop (𝓝 (Y t - Function.leftLim Y t)))
    (f : ℝ → ℝ) (hf : Continuous f)
    (hvanish : ∀ z : ℝ, |z| < ρ → f z = 0) :
    Tendsto (fun n => ∑ i ∈ grid n, f (Y (b n i) - Y (a n i)))
      atTop (𝓝 (∑ t ∈ F, f (Y t - Function.leftLim Y t))) := by
  classical
  have hcross :=
    avram_p2_a_zero_rate_uniform_large_cells_cross_finite_true_jumps
      Y T a b w haT hab hbw hw hL hR ρ hρ F hF
  have hzero : ∀ᶠ n : ℕ in atTop,
      ∀ i ∈ grid n, i ∉ F.image (fun t => idx t n) →
        f (Y (b n i) - Y (a n i)) = 0 := by
    filter_upwards [hcross] with n hn i hi hnot
    by_cases hsmall : |Y (b n i) - Y (a n i)| < ρ
    · exact hvanish _ hsmall
    · have hlarge : ρ ≤ |Y (b n i) - Y (a n i)| :=
        le_of_not_gt hsmall
      obtain ⟨t, htF, htcross⟩ := hn i hlarge
      have heq : i = idx t n := hunique n i t htF htcross
      exact False.elim (hnot (Finset.mem_image.mpr ⟨t, htF, heq.symm⟩))
  exact avram_p2_a_zero_rate_finite_grid_sum_from_selected_cells
    F grid idx (fun n i => Y (b n i) - Y (a n i))
    (fun t => Y t - Function.leftLim Y t)
    f hf hinj hinside hzero hselected
