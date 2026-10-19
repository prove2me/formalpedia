-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousClosedResolventAdjoint.coverFormAdjoint_angularGraphMollifiedPhysicalWeakResolvent_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/37c86891-d343-4097-8f20-4dc4528ab95c

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusWeightedAdjointMollification_coverFormAdjoint_angularGraphMollifiedPhysicalField_eq
import Theorems.Thm_Ehrhart_TorusHomogeneousClosedResolventAdjoint_angularWeakDolbeaultResolvent_closed_mollified_divergence

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusHomogeneousClosedResolventAdjoint
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert DolbeaultRegularity
open WeightedTorusDistributionBridge WeightedDolbeaultBochnerIdentity WeightedTorusDolbeault
open WeightedTorusBrascampLieb TorusWeakDolbeaultMollification TorusFriedrichsMollifierEstimates
open TorusMollifiedBochner TorusWeightedAdjointMollification
open TorusWeightedDensityConvolutionDivergence TorusClosedMollifierAdjoint
open BergmanJetStrictMixedLocalCore
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusHomogeneousClosedResolventAdjoint
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha3 : ContDiff ℝ 3 (angularCoverPotential a))
    (f : angularWeightedScalarL2 a)
    (k : ℕ) (x : LogSpace n) :
    coverFormAdjoint (angularCoverPotential a)
      (angularGraphMollifiedPhysicalField
        (WithLp.snd
          (angularWeakDolbeaultResolvent a f :
            angularDolbeaultGraphAmbient a)) k) x =
      -normalizedCoverMollification
        (complexTorusCoverLift
          (fun q : LogTorus n =>
            (f - angularWeakScalarResolventCLM a f) q)) k x +
        angularMollifiedPhysicalAdjointDriftCommutator
          (WithLp.snd
            (angularWeakDolbeaultResolvent a f :
              angularDolbeaultGraphAmbient a)) k x := by
  rw [coverFormAdjoint_angularGraphMollifiedPhysicalField_eq,
    angularWeakDolbeaultResolvent_closed_mollified_divergence
      ha ha3 f k x]
end Ehrhart.TorusHomogeneousClosedResolventAdjoint
