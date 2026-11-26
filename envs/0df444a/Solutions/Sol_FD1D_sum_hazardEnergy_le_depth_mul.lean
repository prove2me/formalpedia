-- Prove2me | solution 1 for FD1D.sum_hazardEnergy_le_depth_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:05:44.273812+00:00
-- url     : https://prove2.me/submissions/3dd34664-86bb-4060-bf65-881420aa9dcb

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Drift
import Definitions.Def_FD1D_Potential
import Theorems.Thm_FD1D_FiniteLaw_expect_const
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
    {L : ℕ} {h : ∀ d, DyadicNode d → ℝ}
    (hmono : Monotone (hazardEnergy h)) :
    (∑ d ∈ Finset.range L, hazardEnergy h (d + 1)) ≤
      (L : ℝ) * hazardEnergy h L := by
  calc
    (∑ d ∈ Finset.range L, hazardEnergy h (d + 1))
        ≤ ∑ _d ∈ Finset.range L, hazardEnergy h L := by
          apply Finset.sum_le_sum
          intro d hd
          have hdL := Finset.mem_range.mp hd
          exact hmono (by omega)
    _ = (L : ℝ) * hazardEnergy h L := by simp
end FD1D
