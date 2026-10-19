-- Prove2me | solution 1 for Ehrhart.WeightedTorusBochner.angularTorus_weighted_complex_bochner_coordinate_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/e7dd19db-4836-489c-9ec5-aa9d1336b23a

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_integrable_of_continuous_compact_cover
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_weighted_complex_bochner_coordinate_identity_compact_right
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_contDiff_coverAngularSmoothPartition
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_continuous_sourceAngularCutoffLift
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_hasCompactSupport_sourceAngularCutoffLift
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_contDiff_sourceAngularCutoffLift
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_barPartialCoordinate_mul
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_weightedHolomorphicDerivative_mul
import Theorems.Thm_Ehrhart_WeightedTorusDolbeault_continuous_angularCoverPotential
import Theorems.Thm_Ehrhart_WeightedTorusBochner_angular_partitioned_coverWeighted_integral_eq_torus
import Theorems.Thm_Ehrhart_WeightedTorusBochner_angular_integral_holomorphic_coverAngularSmoothPartition_eq_zero
import Theorems.Thm_Ehrhart_WeightedTorusBochner_angular_integral_barPartial_coverAngularSmoothPartition_eq_zero
import Theorems.Thm_Ehrhart_WeightedTorusBochner_integrable_angularHolomorphicPartitionDerivativeLift
import Theorems.Thm_Ehrhart_WeightedTorusBochner_integrable_angularBarPartialPartitionDerivativeLift

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
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    {F G : TorusCharacters.LogSpace n → ℂ}
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hF : ContDiff ℝ 2 F)
    (hG : ContDiff ℝ 2 G)
    (hFp : ∀ q : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift q))
    (hGp : ∀ q : Fin n → ℤ,
      Function.Periodic G
        (TorusCharacters.imaginaryShift q))
    (hGc : HasCompactSupport (torusScalarRepresentative G))
    (i j : Fin n) :
    (∫ p : LogTorus n,
      angularTorusWeightedHolomorphicDerivative a F i p *
        conj (angularTorusWeightedHolomorphicDerivative a G j p)
      ∂(angularWeightedTorusMeasure a)) =
    ∫ p : LogTorus n,
      (sourceTorusBarPartial F j p *
        conj (sourceTorusBarPartial G i p) +
       (torusScalarRepresentative F p *
          angularTorusComplexHessian a i j p) *
            conj (torusScalarRepresentative G p))
      ∂(angularWeightedTorusMeasure a) := by
  let E := TorusCharacters.LogSpace n
  let T := LogTorus n
  let A : E → ℝ := angularCoverPotential a
  let μ : Measure E := coverWeightedMeasure A
  let g : T → ℂ := torusScalarRepresentative G
  let Gcut : E → ℂ := fun z =>
    (coverAngularSmoothPartition z : ℂ) * G z
  let L : T → ℂ := fun p =>
    angularTorusWeightedHolomorphicDerivative a F i p *
      conj (angularTorusWeightedHolomorphicDerivative a G j p)
  let B : T → ℂ := fun p =>
    sourceTorusBarPartial F j p *
      conj (sourceTorusBarPartial G i p)
  let C : T → ℂ := fun p =>
    (torusScalarRepresentative F p *
      angularTorusComplexHessian a i j p) * conj (g p)
  let CL : T → ℂ := fun p =>
    angularTorusWeightedHolomorphicDerivative a F i p * conj (g p)
  let CR : T → ℂ := fun p =>
    sourceTorusBarPartial F j p * conj (g p)
  have hgcont : Continuous g :=
    continuous_torusScalarRepresentative_of_periodic hG.continuous hGp
  have hFcont : Continuous (torusScalarRepresentative F) :=
    continuous_torusScalarRepresentative_of_periodic hF.continuous hFp
  have hgc : HasCompactSupport g := hGc
  have hgconj : HasCompactSupport (fun p : T => conj (g p)) :=
    hasCompactSupport_sourceTorusConj hgc
  have hLc : Continuous L :=
    (continuous_angularTorusWeightedHolomorphicDerivative
      ha2 hF hFp i).mul
      (Complex.continuous_conj.comp
        (continuous_angularTorusWeightedHolomorphicDerivative
          ha2 hG hGp j))
  have hLcompact : HasCompactSupport L := by
    dsimp [L]
    exact (hasCompactSupport_sourceTorusConj
      (hasCompactSupport_angularTorusWeightedHolomorphicDerivative
        a G hGp hGc j)).mul_left
  have hBc : Continuous B :=
    (continuous_sourceTorusBarPartial hF hFp j).mul
      (Complex.continuous_conj.comp
        (continuous_sourceTorusBarPartial hG hGp i))
  have hBcompact : HasCompactSupport B := by
    dsimp [B]
    exact (hasCompactSupport_sourceTorusConj
      (hasCompactSupport_sourceTorusBarPartial
        G hGp hGc i)).mul_left
  have hCc : Continuous C :=
    (hFcont.mul
      (continuous_angularTorusComplexHessian ha2 i j)).mul
      (Complex.continuous_conj.comp hgcont)
  have hCcompact : HasCompactSupport C := by
    dsimp [C]
    exact hgconj.mul_left
  have hCLc : Continuous CL :=
    (continuous_angularTorusWeightedHolomorphicDerivative
      ha2 hF hFp i).mul (Complex.continuous_conj.comp hgcont)
  have hCLcompact : HasCompactSupport CL := by
    dsimp [CL]
    exact hgconj.mul_left
  have hCRc : Continuous CR :=
    (continuous_sourceTorusBarPartial hF hFp j).mul
      (Complex.continuous_conj.comp hgcont)
  have hCRcompact : HasCompactSupport CR := by
    dsimp [CR]
    exact hgconj.mul_left
  have hgrec : complexTorusCoverLift g = G :=
    complexTorusCoverLift_torusScalarRepresentative_eq G hGp
  have hGpoint (z : E) :
      g (complexTorusCoverProjection n z) = G z := by
    exact congrFun hgrec z
  have hFpoint (z : E) :
      torusScalarRepresentative F
        (complexTorusCoverProjection n z) = F z := by
    exact congrFun
      (complexTorusCoverLift_torusScalarRepresentative_eq F hFp) z
  have hHFpoint (z : E) :
      angularTorusWeightedHolomorphicDerivative a F i
        (complexTorusCoverProjection n z) =
        weightedHolomorphicDerivative A F i z := by
    exact congrFun
      (complexTorusCoverLift_torusScalarRepresentative_eq
        (weightedHolomorphicDerivative
          (angularCoverPotential a) F i)
        (fun q => angularWeightedHolomorphicDerivative_periodic
          a F hFp i q)) z
  have hHGpoint (z : E) :
      angularTorusWeightedHolomorphicDerivative a G j
        (complexTorusCoverProjection n z) =
        weightedHolomorphicDerivative A G j z := by
    exact congrFun
      (complexTorusCoverLift_torusScalarRepresentative_eq
        (weightedHolomorphicDerivative
          (angularCoverPotential a) G j)
        (fun q => angularWeightedHolomorphicDerivative_periodic
          a G hGp j q)) z
  have hBFpoint (z : E) :
      sourceTorusBarPartial F j
        (complexTorusCoverProjection n z) =
        barPartialCoordinate F z j := by
    exact congrFun
      (complexTorusCoverLift_torusScalarRepresentative_eq
        (fun w => barPartialCoordinate F w j)
        (fun q => barPartialCoordinate_periodic F hFp j q)) z
  have hBGpoint (z : E) :
      sourceTorusBarPartial G i
        (complexTorusCoverProjection n z) =
        barPartialCoordinate G z i := by
    exact congrFun
      (complexTorusCoverLift_torusScalarRepresentative_eq
        (fun w => barPartialCoordinate G w i)
        (fun q => barPartialCoordinate_periodic G hGp i q)) z
  have hHpoint (z : E) :
      angularTorusComplexHessian a i j
        (complexTorusCoverProjection n z) =
        complexHessian A z i j := by
    exact congrFun
      (complexTorusCoverLift_torusScalarRepresentative_eq
        (fun w => complexHessian (angularCoverPotential a) w i j)
        (fun q => angularComplexHessian_periodic a i j q)) z
  have hcut : sourceAngularCutoffLift g = Gcut := by
    funext z
    change
      (coverAngularSmoothPartition z : ℂ) *
        g (complexTorusCoverProjection n z) =
      (coverAngularSmoothPartition z : ℂ) * G z
    rw [hGpoint z]
  have hGcut : ContDiff ℝ 2 Gcut := by
    rw [← hcut]
    apply contDiff_sourceAngularCutoffLift
    rw [hgrec]
    exact hG
  have hGcutcompact : HasCompactSupport Gcut := by
    rw [← hcut]
    exact hasCompactSupport_sourceAngularCutoffLift hgc
  have hηreal : Differentiable ℝ
      (coverAngularSmoothPartition (n := n)) :=
    (contDiff_coverAngularSmoothPartition
      (n := n) (m := 1)).differentiable (by simp)
  have hηcomplex : Differentiable ℝ
      (fun z : E => (coverAngularSmoothPartition z : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp
      (contDiff_coverAngularSmoothPartition
        (n := n) (m := 1))).differentiable (by simp)
  have hGdiff : Differentiable ℝ G :=
    hG.differentiable (by norm_num)
  have hleftpoint (z : E) :
      weightedHolomorphicDerivative A F i z *
        conj (weightedHolomorphicDerivative A Gcut j z) =
        sourceAngularCutoffLift L z +
          barPartialCoordinate
            (fun w => (coverAngularSmoothPartition w : ℂ)) z j *
              CL (complexTorusCoverProjection n z) := by
    have hp :
        weightedHolomorphicDerivative A Gcut j z =
          (coverAngularSmoothPartition z : ℂ) *
            weightedHolomorphicDerivative A G j z +
            G z * holomorphicCoordinate
              (fun w => (coverAngularSmoothPartition w : ℂ)) z j := by
      exact weightedHolomorphicDerivative_mul A
        hηcomplex hGdiff z j
    rw [hp, map_add, map_mul, map_mul,
      Complex.conj_ofReal,
      conj_holomorphicCoordinate_real hηreal z j]
    dsimp [sourceAngularCutoffLift, L, CL]
    rw [hHFpoint z, hHGpoint z, hGpoint z]
    ring
  have hrightpoint (z : E) :
      (barPartialCoordinate F z j *
        conj (barPartialCoordinate Gcut z i) +
       (F z * complexHessian A z i j) * conj (Gcut z)) =
      sourceAngularCutoffLift (fun p => B p + C p) z +
        holomorphicCoordinate
          (fun w => (coverAngularSmoothPartition w : ℂ)) z i *
            CR (complexTorusCoverProjection n z) := by
    have hp :
        barPartialCoordinate Gcut z i =
          (coverAngularSmoothPartition z : ℂ) *
            barPartialCoordinate G z i +
            G z * barPartialCoordinate
              (fun w => (coverAngularSmoothPartition w : ℂ)) z i := by
      exact barPartialCoordinate_mul hηcomplex hGdiff z i
    rw [hp]
    change
      barPartialCoordinate F z j *
          conj ((coverAngularSmoothPartition z : ℂ) *
            barPartialCoordinate G z i + G z *
              barPartialCoordinate
                (fun w => (coverAngularSmoothPartition w : ℂ)) z i) +
        (F z * complexHessian A z i j) *
          conj ((coverAngularSmoothPartition z : ℂ) * G z) = _
    rw [map_add, map_mul, map_mul, map_mul,
      Complex.conj_ofReal,
      conj_barPartialCoordinate_real hηreal z i]
    dsimp [sourceAngularCutoffLift, B, C, CR]
    rw [hBFpoint z, hBGpoint z, hFpoint z,
      hHpoint z, hGpoint z]
    ring
  have hηL : Integrable (sourceAngularCutoffLift L) μ := by
    exact integrable_of_continuous_compact_cover
      (continuous_angularCoverPotential ha)
      (continuous_sourceAngularCutoffLift hLc)
      (hasCompactSupport_sourceAngularCutoffLift hLcompact)
  have hηR : Integrable
      (sourceAngularCutoffLift (fun p => B p + C p)) μ := by
    exact integrable_of_continuous_compact_cover
      (continuous_angularCoverPotential ha)
      (continuous_sourceAngularCutoffLift (hBc.add hCc))
      (hasCompactSupport_sourceAngularCutoffLift
        (hBcompact.add hCcompact))
  have hcrossL : Integrable
      (fun z : E =>
        barPartialCoordinate
          (fun w => (coverAngularSmoothPartition w : ℂ)) z j *
            CL (complexTorusCoverProjection n z)) μ := by
    exact integrable_angularBarPartialPartitionDerivativeLift
      ha hCLc hCLcompact j
  have hcrossR : Integrable
      (fun z : E =>
        holomorphicCoordinate
          (fun w => (coverAngularSmoothPartition w : ℂ)) z i *
            CR (complexTorusCoverProjection n z)) μ := by
    exact integrable_angularHolomorphicPartitionDerivativeLift
      ha hCRc hCRcompact i
  have hzeroL :
      (∫ z : E,
        barPartialCoordinate
          (fun w => (coverAngularSmoothPartition w : ℂ)) z j *
            CL (complexTorusCoverProjection n z) ∂μ) = 0 :=
    angular_integral_barPartial_coverAngularSmoothPartition_eq_zero
      ha hCLc hCLcompact j
  have hzeroR :
      (∫ z : E,
        holomorphicCoordinate
          (fun w => (coverAngularSmoothPartition w : ℂ)) z i *
            CR (complexTorusCoverProjection n z) ∂μ) = 0 :=
    angular_integral_holomorphic_coverAngularSmoothPartition_eq_zero
      ha hCRc hCRcompact i
  have hboch :=
    weighted_complex_bochner_coordinate_identity_compact_right
      ha2 hF hGcut hGcutcompact i j
  have hleft :
      (∫ z : E,
        weightedHolomorphicDerivative A F i z *
          conj (weightedHolomorphicDerivative A Gcut j z) ∂μ) =
      ∫ z : E, sourceAngularCutoffLift L z ∂μ := by
    calc
      _ = ∫ z : E,
        (sourceAngularCutoffLift L z +
          barPartialCoordinate
            (fun w => (coverAngularSmoothPartition w : ℂ)) z j *
              CL (complexTorusCoverProjection n z)) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with z
        exact hleftpoint z
      _ = (∫ z : E, sourceAngularCutoffLift L z ∂μ) +
          (∫ z : E,
            barPartialCoordinate
              (fun w => (coverAngularSmoothPartition w : ℂ)) z j *
                CL (complexTorusCoverProjection n z) ∂μ) :=
        MeasureTheory.integral_add hηL hcrossL
      _ = _ := by rw [hzeroL, add_zero]
  have hright :
      (∫ z : E,
        (barPartialCoordinate F z j *
          conj (barPartialCoordinate Gcut z i) +
         (F z * complexHessian A z i j) * conj (Gcut z)) ∂μ) =
      ∫ z : E,
        sourceAngularCutoffLift (fun p => B p + C p) z ∂μ := by
    calc
      _ = ∫ z : E,
        (sourceAngularCutoffLift (fun p => B p + C p) z +
          holomorphicCoordinate
            (fun w => (coverAngularSmoothPartition w : ℂ)) z i *
              CR (complexTorusCoverProjection n z)) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with z
        exact hrightpoint z
      _ = (∫ z : E,
          sourceAngularCutoffLift (fun p => B p + C p) z ∂μ) +
        (∫ z : E,
          holomorphicCoordinate
            (fun w => (coverAngularSmoothPartition w : ℂ)) z i *
              CR (complexTorusCoverProjection n z) ∂μ) :=
        MeasureTheory.integral_add hηR hcrossR
      _ = _ := by rw [hzeroR, add_zero]
  have hcover :
      (∫ z : E, sourceAngularCutoffLift L z ∂μ) =
      ∫ z : E,
        sourceAngularCutoffLift (fun p => B p + C p) z ∂μ := by
    exact hleft.symm.trans (hboch.trans hright)
  have hdescL := angular_partitioned_coverWeighted_integral_eq_torus
    ha hLc hLcompact
  have hdescR := angular_partitioned_coverWeighted_integral_eq_torus
    ha (hBc.add hCc) (hBcompact.add hCcompact)
  change
    (∫ p : T, L p ∂(angularWeightedTorusMeasure a)) =
      ∫ p : T, (B p + C p) ∂(angularWeightedTorusMeasure a)
  calc
    _ = logarithmicCoverJacobianFactor n •
      (∫ z : E, sourceAngularCutoffLift L z ∂μ) := hdescL.symm
    _ = logarithmicCoverJacobianFactor n •
      (∫ z : E,
        sourceAngularCutoffLift (fun p => B p + C p) z ∂μ) :=
      congrArg (fun q : ℂ => logarithmicCoverJacobianFactor n • q)
        hcover
    _ = _ := hdescR
end Ehrhart.WeightedTorusBochner
