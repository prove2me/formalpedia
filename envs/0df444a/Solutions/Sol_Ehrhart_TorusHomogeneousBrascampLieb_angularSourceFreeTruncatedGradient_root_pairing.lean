-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousBrascampLieb.angularSourceFreeTruncatedGradient_root_pairing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/cbecf19c-0a13-4407-a65e-dc0dc8be4e14

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_RadialPhysicalInverseSquareRootEnergy_complexPositiveInverseSquareRootAction_pairing
import Theorems.Thm_Ehrhart_TorusHomogeneousBrascampLieb_angularSourceFreeTruncatedGradientL2_ae_eq

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusHomogeneousBrascampLieb
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert WeightedBrascampLieb WeightedResolventConstantCore
open EqualitySaturatingKillingPaths ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity
open MatrixTorusBochnerIdentity MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault WeightedTorusBrascampLieb
open MatrixTorusDolbeaultGraph TorusDeckGraphAdjoint TorusFriedrichsCutoff
open RadialPhysicalVelocityCompactGraph RadialPhysicalInverseSquareRootEnergy
open RadialPhysicalResolventRootCutoffPairing RadialPhysicalResolventDefectReduction
open TorusHomogeneousWeakResolventRootCoercivity
open scoped BigOperators ENNReal ComplexConjugate ComplexOrder
  MatrixOrder InnerProductSpace Topology ContDiff
namespace Ehrhart.TorusHomogeneousBrascampLieb
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    {U : LogSpace n → ℂ} (hU : ContDiff ℝ 3 U)
    (hperiod : ∀ d : Fin n → ℤ, Function.Periodic U (imaginaryShift d))
    (hu : MemLp (torusScalarRepresentative U) 2
      (angularWeightedTorusMeasure a))
    (hr : MemLp (angularSourceFreeInverseRootGradientField a U)
      2 (angularWeightedTorusMeasure a))
    (W : angularWeightedFormL2 a) (m : ℕ) :
    @inner ℂ (angularWeightedFormL2 a) _ W
      (angularSourceFreeTruncatedGradientL2
        ha hU hperiod hu m) =
    @inner ℂ (angularWeightedFormL2 a) _
      (angularSourceFreeInverseRootGradientL2 hr)
      (angularPhysicalResolventRootCutoffL2 ha2 hH W m) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [angularSourceFreeTruncatedGradientL2_ae_eq
      ha hU hperiod hu m,
     hr.coeFn_toLp,
     (angularPhysicalResolventRootCutoffField_memLp
       ha2 hH W m).coeFn_toLp]
      with q hrow hinv hroot
  change
    @inner ℂ (EuclideanSpace ℂ (Fin n)) _ (W q)
      (angularSourceFreeTruncatedGradientL2
        ha hU hperiod hu m q) =
    @inner ℂ (EuclideanSpace ℂ (Fin n)) _
      (angularSourceFreeInverseRootGradientL2 hr q)
      (angularPhysicalResolventRootCutoffL2 ha2 hH W m q)
  rw [hrow]
  change
    @inner ℂ (EuclideanSpace ℂ (Fin n)) _ (W q)
      ((sourceRadialCutoff m q : ℂ) •
        torusFunctionBarPartialRepresentative U q) =
    @inner ℂ (EuclideanSpace ℂ (Fin n)) _
      (hr.toLp (angularSourceFreeInverseRootGradientField a U) q)
      ((angularPhysicalResolventRootCutoffField_memLp
        ha2 hH W m).toLp
          (angularPhysicalResolventRootCutoffField a W m) q)
  rw [hinv, hroot]
  unfold angularPhysicalResolventRootCutoffField
    angularSourceFreeInverseRootGradientField
  rw [inner_smul_right, inner_smul_right]
  congr 1
  change
    @inner ℂ (EuclideanSpace ℂ (Fin n)) _ (W q)
      (torusFunctionBarPartialRepresentative U q) =
    @inner ℂ (EuclideanSpace ℂ (Fin n)) _
      (Matrix.toEuclideanLin
        ((CFC.sqrt (angularTorusComplexHessianMatrix a q))⁻¹)
        (WithLp.toLp 2
          (star (fun i => torusFunctionBarPartialRepresentative U q i))))
      (Matrix.toEuclideanLin
        (CFC.sqrt (angularTorusComplexHessianMatrix a q))
        (angularEuclideanConjugation (W q)))
  rw [complexPositiveInverseSquareRootAction_pairing
    (hH q)
    (fun i => torusFunctionBarPartialRepresentative U q i)
    (angularEuclideanConjugation (W q)),
    EuclideanSpace.inner_eq_star_dotProduct]
  rfl
end Ehrhart.TorusHomogeneousBrascampLieb
