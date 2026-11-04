-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_finite_actual_jumps_exclude_spurious_large_cells
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:43:59.372819+00:00
-- url     : https://prove2.me/submissions/6652937d-b448-4491-8609-471b5acd5de7

import Mathlib.Topology.Order.LeftRightLim
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_large_shrinking_cells_pinpoint_true_jump
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal

theorem solution
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0)
    (a b w : ℕ → ℝ≥0)
    (haT : ∀ n, a n ≤ T)
    (hab : ∀ n, a n ≤ b n)
    (hbw : ∀ n, b n ≤ a n + w n)
    (hw : Tendsto w atTop (𝓝 (0 : ℝ≥0)))
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t)
    (ρ : ℝ) (hρ : 0 < ρ)
    (F : Finset ℝ≥0)
    (hF : ∀ t ∈ Icc (0 : ℝ≥0) T,
       ρ ≤ |Y t - Function.leftLim Y t| → t ∈ F)
    (havoid : ∀ n, ∀ t ∈ F, ¬ (a n < t ∧ t ≤ b n))
    (hlarge : ∀ n, ρ ≤ |Y (b n) - Y (a n)|) :
    False := by
  obtain ⟨t, ht, hj, φ, _hφ, hcross⟩ :=
    avram_p2_a_zero_rate_large_shrinking_cells_pinpoint_true_jump
      Y T a b w haT hab hbw hw hL hR ρ hρ hlarge
  exact (havoid (φ 0) t (hF t ht hj)) (hcross 0)
