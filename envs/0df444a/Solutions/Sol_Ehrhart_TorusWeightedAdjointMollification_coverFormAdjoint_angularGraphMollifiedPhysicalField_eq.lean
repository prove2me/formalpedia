-- Prove2me | solution 1 for Ehrhart.TorusWeightedAdjointMollification.coverFormAdjoint_angularGraphMollifiedPhysicalField_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/f278e108-eb8b-49fe-b8bc-0d691f79735f

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusWeightedAdjointMollification
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert WeightedTorusDistributionBridge
open WeightedDolbeaultBochnerIdentity WeightedTorusDolbeault TorusWeakDolbeaultMollification
open TorusFriedrichsMollifierEstimates TorusMollifiedBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusWeightedAdjointMollification
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a) (k : ℕ) (x : LogSpace n) :
    coverFormAdjoint (angularCoverPotential a)
      (angularGraphMollifiedPhysicalField W k) x =
      (∑ j : Fin n,
        (holomorphicCoordinate
          (normalizedCoverMollification
            (complexTorusCoverLift
              (fun q : LogTorus n =>
                (W q : EuclideanSpace ℂ (Fin n)) j)) k)
          x j -
        normalizedCoverMollification
          (fun y : LogSpace n =>
            holomorphicCoordinate
              (fun v => (angularCoverPotential a v : ℂ)) y j *
              complexTorusCoverLift
                (fun q : LogTorus n =>
                  (W q : EuclideanSpace ℂ (Fin n)) j) y) k x)) +
      angularMollifiedPhysicalAdjointDriftCommutator W k x := by
  simp only [coverFormAdjoint, weightedHolomorphicDerivative,
    angularGraphMollifiedPhysicalField,
    angularMollifiedPhysicalAdjointDriftCommutator,
    normalizedCoverComplexDriftCommutator,
    Finset.sum_sub_distrib]
  have hcomm :
      (∑ j : Fin n,
        normalizedCoverMollification
          (complexTorusCoverLift
            (fun q : LogTorus n =>
              (W q : EuclideanSpace ℂ (Fin n)) j)) k x *
          holomorphicCoordinate
            (fun y => (angularCoverPotential a y : ℂ)) x j) =
      (∑ j : Fin n,
        holomorphicCoordinate
          (fun y => (angularCoverPotential a y : ℂ)) x j *
        normalizedCoverMollification
          (complexTorusCoverLift
            (fun q : LogTorus n =>
              (W q : EuclideanSpace ℂ (Fin n)) j)) k x) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hcomm]
  ring
end Ehrhart.TorusWeightedAdjointMollification
