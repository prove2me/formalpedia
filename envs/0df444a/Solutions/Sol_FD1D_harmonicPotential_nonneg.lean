-- Prove2me | solution 1 for FD1D.harmonicPotential_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:22:38.539803+00:00
-- url     : https://prove2.me/submissions/71de2c50-66e7-428c-ad32-c12aa40e1965

import Definitions.Def_FD1D_Potential
import Definitions.Def_FD1D_Parameters
import Definitions.Def_FD1D_PotentialBounds
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_harmonicPotential_zero
import Theorems.Thm_FD1D_leafCount_eq_pow
import Theorems.Thm_FD1D_natFloor_parameterRatio
import Theorems.Thm_FD1D_policyA_eq_parameterA
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.harmonicPotential_zero
attribute [local simp] FD1D.leafCount_eq_pow
attribute [local simp] FD1D.natFloor_parameterRatio
attribute [local simp] FD1D.policyA_eq_parameterA
attribute [local simp] FD1D.weightedLevel_zero



set_option autoImplicit true
open FD1D
noncomputable section
open Set intervalIntegral
open scoped BigOperators
namespace FD1D
theorem _root_.solution {a : ℝ} (ha : 0 < a) (k : ℕ) :
    0 ≤ harmonicPotential a k := by
  unfold harmonicPotential
  apply Finset.sum_nonneg
  intro j hj
  simp only [Finset.mem_Icc] at hj
  positivity
end FD1D
