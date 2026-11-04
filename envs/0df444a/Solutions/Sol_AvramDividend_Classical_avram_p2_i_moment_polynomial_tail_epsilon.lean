-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_polynomial_tail_epsilon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:20:00.074875+00:00
-- url     : https://prove2.me/submissions/5a75fe23-be59-4299-9635-09131c8d80f7

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_finite_polynomial_tail_epsilon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped BigOperators

theorem solution
    (p : Polynomial ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, p.natDegree ≤ K ∧ ∀ z : ℝ, 2 ≤ z →
      |p.eval z| ≤ ε * z ^ K := by
  classical
  have hs : ∀ j ∈ p.support, j ≤ p.natDegree := by
    intro j hj
    have hmem : j ∈ Finset.range (p.natDegree + 1) :=
      Polynomial.supp_subset_range_natDegree_succ hj
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hmem)
  obtain ⟨K, hK, hbound⟩ :=
    AvramDividend.Classical.avram_p2_i_moment_finite_polynomial_tail_epsilon
      p.support p.coeff p.natDegree hs ε hε
  refine ⟨K, hK, ?_⟩
  intro z hz
  have heval : p.eval z =
      ∑ j ∈ p.support, p.coeff j * z ^ j := by
    rw [Polynomial.eval_eq_sum]
    rfl
  rw [heval]
  exact hbound z hz
