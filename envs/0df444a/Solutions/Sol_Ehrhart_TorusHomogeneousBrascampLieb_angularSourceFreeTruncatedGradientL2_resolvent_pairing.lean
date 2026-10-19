-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousBrascampLieb.angularSourceFreeTruncatedGradientL2_resolvent_pairing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/61871a4c-733c-4efc-82ab-ad7698e6258b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusDeckGraphAdjoint_angularWeakDolbeaultResolvent_smoothGraphTest_adjoint

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
    {U : LogSpace n → ℂ} (hU : ContDiff ℝ 3 U)
    (hperiod : ∀ d : Fin n → ℤ, Function.Periodic U (imaginaryShift d))
    (hu : MemLp (torusScalarRepresentative U) 2
      (angularWeightedTorusMeasure a))
    (m : ℕ) (g : angularWeightedScalarL2 a) :
    @inner ℂ (angularWeightedFormL2 a) _
      (WithLp.snd
        (angularWeakDolbeaultResolvent a g :
          angularDolbeaultGraphAmbient a))
      (angularSourceFreeTruncatedGradientL2
        ha hU hperiod hu m) =
    @inner ℂ (angularWeightedScalarL2 a) _
      (g - angularWeakScalarResolventCLM a g)
      (angularScalarL2OfRepresentative a
        (angularSourceFreeScalarRadialGraphTest U m)
        (angularSourceFreeScalarRadialGraphTest_scalar_memLp
          ha hU hperiod m)) -
    @inner ℂ (angularWeightedFormL2 a) _
      (WithLp.snd
        (angularWeakDolbeaultResolvent a g :
          angularDolbeaultGraphAmbient a))
      ((angularSourceFreeScalarCutoffGradient_memLp
        hU hperiod hu m).toLp
          (angularSourceFreeScalarCutoffGradient U m)) := by
  unfold angularSourceFreeTruncatedGradientL2
  rw [inner_sub_right]
  rw [angularWeakDolbeaultResolvent_smoothGraphTest_adjoint a g
    (angularSourceFreeScalarRadialGraphTest U m)
    (contDiff_angularSourceFreeScalarRadialGraphTest hU m)
    (angularSourceFreeScalarRadialGraphTest_periodic hperiod m)
    (hasCompactSupport_angularSourceFreeScalarRadialGraphTest U m)
    (angularSourceFreeScalarRadialGraphTest_scalar_memLp
      ha hU hperiod m)
    (angularSourceFreeScalarRadialGraphTest_barPartial_memLp
      ha hU hperiod m)]
end Ehrhart.TorusHomogeneousBrascampLieb
