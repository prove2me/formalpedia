-- Prove2me | solution 1 for Ehrhart.JetEnvelopeTrueRadialMollifier.integral_sourceJointComplexPhase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/074cbdb2-ce97-4106-b7dd-5face7e0b9ad

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JetEnvelopeTrueRadialMollifier_measurePreserving_sourceJointComplexPhase
import Theorems.Thm_Ehrhart_JetEnvelopeTrueRadialMollifier_measurableEmbedding_sourceJointComplexPhase

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.JetEnvelopeTrueRadialMollifier
open Set Filter Function MeasureTheory Metric
open JetEnvelopeGlobalPlurisubharmonic
open scoped BigOperators Topology ENNReal InnerProductSpace Convolution ContDiff
attribute [local instance] Ehrhart.JetEnvelopeTrueRadialMollifier.sourceJointCoverVolume_isAddHaar
namespace Ehrhart.JetEnvelopeTrueRadialMollifier
theorem _root_.solution {n : ℕ}
    (u : ℂ) (hu : ‖u‖ = 1)
    (g : SourceJointComplexCover n → ℝ) :
    (∫ y : SourceJointComplexCover n, g (u • y)) =
      ∫ y : SourceJointComplexCover n, g y :=
  (measurePreserving_sourceJointComplexPhase u hu).integral_comp
    (measurableEmbedding_sourceJointComplexPhase u hu) g
end Ehrhart.JetEnvelopeTrueRadialMollifier
