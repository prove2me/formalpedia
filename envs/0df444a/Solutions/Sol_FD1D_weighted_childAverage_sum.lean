-- Prove2me | solution 1 for FD1D.weighted_childAverage_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:50:24.509498+00:00
-- url     : https://prove2.me/submissions/609c618b-6111-4898-b8bb-2c221da0d708

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
import Theorems.Thm_FD1D_sum_children
import Theorems.Thm_FD1D_weightedLevel_zero
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const


attribute [local simp] FD1D.weightedLevel_zero

set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution
    (f : ∀ d, DyadicNode d → ℝ) (d : ℕ) :
    ∑ v, nodeMass d v * childAverage f d v = weightedLevel f (d + 1) := by
  rw [weightedLevel, sum_children]
  apply Finset.sum_congr rfl
  intro v _
  simp only [childAverage, nodeMass_leftChild, nodeMass_rightChild]
  ring
end FD1D
