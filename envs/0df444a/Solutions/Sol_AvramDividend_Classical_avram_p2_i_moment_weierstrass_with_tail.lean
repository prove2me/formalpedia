-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_weierstrass_with_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:23:09.903588+00:00
-- url     : https://prove2.me/submissions/58d8dba0-cf0a-4df7-9020-68b45f50ac0b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_polynomial_tail_epsilon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology

theorem solution
    (g : ℝ → ℝ) (hg : ContinuousOn g (Set.Icc (0 : ℝ) 2))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Polynomial ℝ,
      (∀ z ∈ Set.Icc (0 : ℝ) 2, |p.eval z - g z| < ε) ∧
      (∃ K : ℕ, p.natDegree ≤ K ∧
        ∀ z : ℝ, 2 ≤ z → |p.eval z| ≤ ε * z ^ K) := by
  obtain ⟨p, hp⟩ :=
    exists_polynomial_near_of_continuousOn (0 : ℝ) (2 : ℝ) g hg ε hε
  refine ⟨p, hp, ?_⟩
  exact AvramDividend.Classical.avram_p2_i_moment_polynomial_tail_epsilon p ε hε
