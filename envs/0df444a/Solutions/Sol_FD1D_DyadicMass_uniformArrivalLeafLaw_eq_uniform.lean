-- Prove2me | solution 1 for FD1D.DyadicMass.uniformArrivalLeafLaw_eq_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:05:56.943314+00:00
-- url     : https://prove2.me/submissions/efbb9c51-1234-40f3-96ce-6bbb3d653237

import Definitions.Def_FD1D_Spatial
import Definitions.Def_FD1D_UniformArrival
import Theorems.Thm_FD1D_DyadicMass_uniformArrivalMass_piecewiseCDF
import Theorems.Thm_FD1D_DyadicMass_uniformArrivalMass_quantile
import Theorems.Thm_FD1D_DeletionRule_kernel_apply
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_SupplyConfiguration_countState_apply
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.DeletionRule.kernel_apply
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.SupplyConfiguration.countState_apply
attribute [local simp] FD1D.weightedLevel_zero


attribute [local simp] FD1D.DyadicMass.uniformArrivalMass_piecewiseCDF
attribute [local simp] FD1D.DyadicMass.uniformArrivalMass_quantile

set_option autoImplicit true
open FD1D
noncomputable section
open Set MeasureTheory
open FD1D.DyadicMass
namespace FD1D.DyadicMass
theorem _root_.solution (L : ℕ) :
    uniformArrivalLeafLaw L =
      (FiniteLaw.uniform : FiniteLaw (DyadicNode L)) := by
  apply FiniteLaw.ext
  intro i
  simp [uniformArrivalLeafLaw]
end FD1D.DyadicMass
