-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousBrascampLieb.tendsto_angularSourceFreeResolventRootCutoff_pairing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/6a86ce61-e0eb-4543-b983-2769dcf39871

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusHomogeneousBrascampLieb_tendsto_angularSourceFreeTruncatedGradient_resolvent_pairing
import Theorems.Thm_Ehrhart_TorusHomogeneousBrascampLieb_angularSourceFreeTruncatedGradient_root_pairing

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
    (g : angularWeightedScalarL2 a) :
    Tendsto
      (fun m : ℕ =>
        @inner ℂ (angularWeightedFormL2 a) _
          (angularSourceFreeInverseRootGradientL2 hr)
          (angularPhysicalResolventRootCutoffL2 ha2 hH
            (WithLp.snd
              (angularWeakDolbeaultResolvent a g :
                angularDolbeaultGraphAmbient a)) m))
      atTop
      (nhds
        (@inner ℂ (angularWeightedScalarL2 a) _
          (g - angularWeakScalarResolventCLM a g)
          (hu.toLp (torusScalarRepresentative U)))) := by
  apply Filter.Tendsto.congr' _
    (tendsto_angularSourceFreeTruncatedGradient_resolvent_pairing
      ha hU hperiod hu g)
  filter_upwards [] with m
  exact angularSourceFreeTruncatedGradient_root_pairing
    ha ha2 hH hU hperiod hu hr
    (WithLp.snd
      (angularWeakDolbeaultResolvent a g :
        angularDolbeaultGraphAmbient a)) m
end Ehrhart.TorusHomogeneousBrascampLieb
