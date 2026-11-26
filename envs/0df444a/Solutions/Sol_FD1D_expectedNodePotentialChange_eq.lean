-- Prove2me | solution 1 for FD1D.expectedNodePotentialChange_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:05:21.673777+00:00
-- url     : https://prove2.me/submissions/47c609eb-2b6d-460e-9445-fbff281f1ae7

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Drift
import Definitions.Def_FD1D_Potential
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_harmonicPotential_succ
import Theorems.Thm_FD1D_harmonicPotential_zero
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
    {a p q : ℝ} {N : ℕ}
    (hzero : N = 0 → q = 0) :
    expectedNodePotentialChange a N p q =
      p * (1 - q) / (N + a + 1) -
        q * (1 - p) / (N + a) := by
  rcases N with _ | N
  · simp [expectedNodePotentialChange, bernoulliMass, updateCount, hzero rfl,
      harmonicPotential_succ]
    simp [div_eq_mul_inv, add_comm]
  · simp [expectedNodePotentialChange, bernoulliMass, updateCount,
      harmonicPotential_succ]
    ring
end FD1D
