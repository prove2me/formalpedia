-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerIdentity.integrable_sourceAngularDerivativeLift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/b4f39f59-b1d3-4df4-9a26-38ef141aecfd

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_coverWeightedMeasure_isLocallyFinite
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_continuous_sourceAngularDerivativeLift
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_hasCompactSupport_sourceAngularDerivativeLift

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
    {n : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hf : Continuous f)
    (hfc : HasCompactSupport f)
    (v : TorusCharacters.LogSpace n) :
    Integrable (sourceAngularDerivativeLift f v)
      (coverWeightedMeasure (matrixSourceCoverPotential φ)) := by
  let : IsLocallyFiniteMeasure
      (coverWeightedMeasure (matrixSourceCoverPotential φ)) :=
    coverWeightedMeasure_isLocallyFinite
      (continuous_matrixSourceCoverPotential hφ)
  exact (continuous_sourceAngularDerivativeLift
    hf v).integrable_of_hasCompactSupport
      (hasCompactSupport_sourceAngularDerivativeLift hfc v)
end Ehrhart.MatrixTorusBochnerIdentity
