-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_actual_grid_partial_negative_large_mark_count_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:31:14.250034+00:00
-- url     : https://prove2.me/submissions/e0e40f08-209e-4960-bca7-7ee7c7b83467

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_random_clock_clipped_separated_jump_count_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ρ : Ω → ℝ≥0) (ω : Ω)
    (g : ℕ → ℝ≥0) (hg : Monotone g) (i : ℕ)
    (η : ℝ) (hη : 0 < η) :
    ((Measure.count.restrict
      {u : ℝ≥0 | 0 < u ∧ X.X u ω -
         Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (min (g i) (ρ ω)) (min (g (i+1)) (ρ ω)) ×ˢ
        {z : ℝ | η ≤ dist z 0}) < ⊤ := by
  have hSource :=
    AvramDividend.Classical.avram_wave5_01_actual_source_random_clock_clipped_separated_jump_count_finite
      X ω (g i) (g (i+1)) ρ η hη
  by_cases h : ρ ω ≤ g i
  · have hn : ρ ω ≤ g (i+1) := h.trans (hg (Nat.le_succ i))
    simp only [min_eq_right h, min_eq_right hn, Set.Ioc_self, Set.empty_prod,
      measure_empty, ENNReal.zero_lt_top]
  · have hleft : min (g i) (ρ ω) = g i :=
      min_eq_left (le_of_lt (lt_of_not_ge h))
    simpa only [hleft, min_comm (ρ ω) (g (i+1))] using hSource

