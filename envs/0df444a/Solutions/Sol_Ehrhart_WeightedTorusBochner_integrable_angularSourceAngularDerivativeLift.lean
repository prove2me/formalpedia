-- Prove2me | solution 1 for Ehrhart.WeightedTorusBochner.integrable_angularSourceAngularDerivativeLift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/668754a1-20ca-4545-a80d-60065a4c4b30

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_integrable_of_continuous_compact_cover
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_continuous_sourceAngularDerivativeLift
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_hasCompactSupport_sourceAngularDerivativeLift
import Theorems.Thm_Ehrhart_WeightedTorusDolbeault_continuous_angularCoverPotential

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusBochner
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert JetEnvelopeSlopeConvergence EqualitySaturatingKillingPaths
open ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity WeightedTorusDistributionBridge
open WeightedTorusGraphWeakBridge MatrixTorusBochnerBridge MatrixTorusBochnerIdentity
open WeightedTorusDolbeault
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.WeightedTorusBochner
theorem _root_.solution {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    {f : LogTorus n → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f)
    (v : TorusCharacters.LogSpace n) :
    Integrable (sourceAngularDerivativeLift f v)
      (coverWeightedMeasure (angularCoverPotential a)) := by
  exact integrable_of_continuous_compact_cover
    (continuous_angularCoverPotential ha)
    (continuous_sourceAngularDerivativeLift hf v)
    (hasCompactSupport_sourceAngularDerivativeLift hfc v)
end Ehrhart.WeightedTorusBochner
