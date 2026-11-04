-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_compact_test_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:31:35.46653+00:00
-- url     : https://prove2.me/submissions/e99f85e7-4d7e-47cf-a273-516604978a5a

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology

theorem solution
    (μ : Measure ℝ) (hfinite : μ Set.univ < ⊤)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hg0 : ∀ z : ℝ, z ≤ 0 ∨ 1 ≤ z → g z = 0) :
    Integrable g μ := by
  have hcs : HasCompactSupport g := by
    apply HasCompactSupport.intro (K := Set.Icc (0 : ℝ) 1) isCompact_Icc
    intro z hz
    have hout : z ≤ 0 ∨ 1 ≤ z := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hz
      rcases hz with hz | hz
      · exact Or.inl (le_of_lt hz)
      · exact Or.inr (le_of_lt hz)
    exact hg0 z hout
  letI : IsFiniteMeasure μ := ⟨hfinite⟩
  exact hg.integrable_of_hasCompactSupport hcs
