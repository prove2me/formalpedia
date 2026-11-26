-- Prove2me | solution 1 for FD1D.potentialRemainder_le_sum_hazardEnergy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:07:01.152635+00:00
-- url     : https://prove2.me/submissions/57434358-319c-4ca3-b4ca-37ea4785e5c1

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Drift
import Definitions.Def_FD1D_Potential
import Theorems.Thm_FD1D_potentialRemainder_summand_le
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_harmonicPotential_zero
import Theorems.Thm_FD1D_nodeMass_nonneg
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
    {q h : ∀ d, DyadicNode d → ℝ}
    (ha : 0 < a)
    (hq0 : ∀ d v, 0 ≤ q d v)
    (hq1 : ∀ d v, q d v ≤ 1)
    (hmajor : ∀ d v,
      nodeMass d v ≤ ((N d v : ℝ) + a) * h d v) :
    potentialRemainder L a N q ≤
      ∑ d ∈ Finset.range L, hazardEnergy h (d + 1) := by
  unfold potentialRemainder
  apply Finset.sum_le_sum
  intro d hd
  simp only [hazardEnergy, weightedLevel]
  apply Finset.sum_le_sum
  intro v hv
  exact potentialRemainder_summand_le
    (nodeMass_nonneg _ _) (hq0 _ _) (hq1 _ _) (by positivity)
    (hmajor _ _)
end FD1D
