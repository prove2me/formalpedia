-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerIdentity.fderiv_angularSmoothPartition_eq_zero_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/653d44fe-b3ce-434c-bd39-a70b884889ec

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_angularSmoothPartition_nonneg

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MatrixTorusBochnerIdentity
open Set Function MeasureTheory Filter Matrix
open EqualitySaturatingKillingPaths WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity MatrixTorusBochnerBridge
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.MatrixTorusBochnerIdentity
theorem _root_.solution
    {n : ℕ} {t : Space n}
    (ht : angularSmoothPartition t = 0) :
    fderiv ℝ (angularSmoothPartition (n := n)) t = 0 := by
  have hmin : IsLocalMin (angularSmoothPartition (n := n)) t := by
    change ∀ᶠ s : Space n in 𝓝 t,
      angularSmoothPartition t ≤ angularSmoothPartition s
    exact Filter.Eventually.of_forall (fun s => by
      rw [ht]
      exact angularSmoothPartition_nonneg s)
  exact hmin.fderiv_eq_zero
end Ehrhart.MatrixTorusBochnerIdentity
