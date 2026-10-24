-- Prove2me | solution 1 for AvramDividend.Classical.finite_grid_two_sided_hitting_eq_upper_hitting_for_remote_lower_corrected
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T08:13:46.471769+00:00
-- url     : https://prove2.me/submissions/7c5cc55f-be6c-4b37-b792-aad31cce42d7

import Mathlib.Probability.Process.HittingTime
import Theorems.Thm_AvramDividend_Classical_finite_grid_lower_barrier_eventually_irrelevant_corrected
import Theorems.Thm_AvramDividend_Classical_chat03_hittingBtwn_congr_before_terminal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (f : ℕ → Ω → ℝ) (ω : Ω) (z : ℝ) (m : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      hittingBtwn
        (fun k ω => max (f k ω - z) (-(n : ℝ) - f k ω))
        (Ioi (0 : ℝ)) 0 m ω =
      hittingBtwn
        (fun k ω => f k ω - z)
        (Ioi (0 : ℝ)) 0 m ω := by
  obtain ⟨N, hN⟩ :=
    AvramDividend.Classical.finite_grid_lower_barrier_eventually_irrelevant_corrected
      (fun k => f k ω) z m
  refine ⟨N, ?_⟩
  intro n hn
  apply AvramDividend.Classical.chat03_hittingBtwn_congr_before_terminal
  intro j hj
  simpa only [mem_Ioi, lt_max_iff, sub_pos] using
    (hN n hn j (Nat.le_of_lt hj))
