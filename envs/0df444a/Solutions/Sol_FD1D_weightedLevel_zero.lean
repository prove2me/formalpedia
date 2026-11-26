-- Prove2me | solution 1 for FD1D.weightedLevel_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:49:10.519396+00:00
-- url     : https://prove2.me/submissions/417265e7-1dd7-407e-bd17-dfde2a4ae6a7

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution (f : ∀ d, DyadicNode d → ℝ) :
    weightedLevel f 0 = f 0 dyadicRoot := by
  unfold weightedLevel
  change (∑ v : Fin 1, nodeMass 0 v * f 0 v) = f 0 dyadicRoot
  rw [Fin.sum_univ_one]
  simp [nodeMass, dyadicRoot]
end FD1D
