-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerIdentity.sourceTorusFormExterior_add_mixed_eq_full
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/17987fc7-8d5b-46cb-980b-2a3d2cb37688

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_antisymmetric_matrix_energy_add_cross

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
    {n : ℕ}
    (W : TorusCharacters.LogSpace n → Fin n → ℂ)
    (p : WeightedTorusHilbert.LogTorus n) :
    sourceTorusFormExteriorDerivativeDensity W p +
      sourceTorusFormMixedDerivativeDensity W p =
        sourceTorusFormFullDerivativeDensity W p := by
  exact antisymmetric_matrix_energy_add_cross
    (fun i j => sourceTorusBarPartial (fun z => W z i) j p)
end Ehrhart.MatrixTorusBochnerIdentity
