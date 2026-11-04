-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_eventually_small_nonjump_source_grid_cells
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:49:56.199693+00:00
-- url     : https://prove2.me/submissions/0d88e84d-3d31-4614-a456-b768a4d5a5ce

import Mathlib.Topology.Order.LeftRightLim
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_frequently_bad_source_grid_cells_impossible
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal

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
    (havoid : ∀ n i, ∀ t ∈ F, ¬ (a n i < t ∧ t ≤ b n i)) :
    ∀ᶠ n in (atTop : Filter ℕ),
      ∀ i, |Y (b n i) - Y (a n i)| < ρ := by
  by_contra hnot
  have hfreq : ∃ᶠ n in (atTop : Filter ℕ),
      ¬∀ i, |Y (b n i) - Y (a n i)| < ρ :=
    (Filter.not_eventually).mp hnot
  have hbad : ∃ᶠ n in (atTop : Filter ℕ),
      ∃ i, ρ ≤ |Y (b n i) - Y (a n i)| := by
    simpa only [not_forall, not_lt] using hfreq
  exact avram_p2_a_zero_rate_frequently_bad_source_grid_cells_impossible
    Y T a b w haT hab hbw hw hL hR ρ hρ F hF havoid hbad
