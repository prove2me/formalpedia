-- Prove2me | solution 1 for FD1D.expectedGlobalPotentialChange_eq_drift_sub_remainder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:57:07.836951+00:00
-- url     : https://prove2.me/submissions/bb0dbff5-8acc-4fc3-94d2-b08df72b10a6

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Drift
import Definitions.Def_FD1D_Potential
import Theorems.Thm_FD1D_expectedNodePotentialChange_eq
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_harmonicPotential_zero
import Theorems.Thm_FD1D_node_harmonic_drift_identity
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.harmonicPotential_zero
attribute [local simp] FD1D.weightedLevel_zero



set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
namespace FD1D
theorem _root_.solution
    {L : ℕ} {a : ℝ} {N : ∀ d, DyadicNode d → ℕ}
    {q : ∀ d, DyadicNode d → ℝ}
    (ha : 0 < a)
    (hzero : ∀ d v, N d v = 0 → q d v = 0) :
    expectedGlobalPotentialChange L a N q =
      potentialDrift L a N q - potentialRemainder L a N q := by
  have hden (d : ℕ) (v : DyadicNode d) :
      (N d v : ℝ) + a ≠ 0 := by positivity
  have hden1 (d : ℕ) (v : DyadicNode d) :
      (N d v : ℝ) + a + 1 ≠ 0 := by positivity
  simp_rw [expectedGlobalPotentialChange, expectedNodePotentialChange_eq
    (hzero _ _), node_harmonic_drift_identity _ _ _ _
      (hden _ _) (hden1 _ _)]
  simp only [potentialDrift, bellmanDrift, potentialRemainder]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  apply congrArg₂ (· - ·)
  · apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro v hv
    ring
  · apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro v hv
    ring
end FD1D
