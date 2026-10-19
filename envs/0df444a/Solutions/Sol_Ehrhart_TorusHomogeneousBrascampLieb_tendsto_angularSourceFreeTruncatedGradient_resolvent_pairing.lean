-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousBrascampLieb.tendsto_angularSourceFreeTruncatedGradient_resolvent_pairing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/70e7f964-49d1-4fef-aedf-109c38d2da8c

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusHomogeneousBrascampLieb_angularSourceFreeScalarCutoffGradient_L2_tendsto_zero
import Theorems.Thm_Ehrhart_TorusHomogeneousBrascampLieb_angularSourceFreeScalarRadialGraphTest_scalar_L2_tendsto
import Theorems.Thm_Ehrhart_TorusHomogeneousBrascampLieb_angularSourceFreeTruncatedGradientL2_resolvent_pairing

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
    (g : angularWeightedScalarL2 a) :
    Tendsto
      (fun m : ℕ =>
        @inner ℂ (angularWeightedFormL2 a) _
          (WithLp.snd
            (angularWeakDolbeaultResolvent a g :
              angularDolbeaultGraphAmbient a))
          (angularSourceFreeTruncatedGradientL2 ha hU hperiod hu m))
      atTop
      (nhds
        (@inner ℂ (angularWeightedScalarL2 a) _
          (g - angularWeakScalarResolventCLM a g)
          (hu.toLp (torusScalarRepresentative U)))) := by
  let W : angularWeightedFormL2 a :=
    WithLp.snd
      (angularWeakDolbeaultResolvent a g :
        angularDolbeaultGraphAmbient a)
  let d : angularWeightedScalarL2 a :=
    g - angularWeakScalarResolventCLM a g
  have hfirst :
      Tendsto
        (fun m : ℕ =>
          @inner ℂ (angularWeightedScalarL2 a) _ d
            (angularScalarL2OfRepresentative a
              (angularSourceFreeScalarRadialGraphTest U m)
              (angularSourceFreeScalarRadialGraphTest_scalar_memLp
                ha hU hperiod m)))
        atTop
        (nhds
          (@inner ℂ (angularWeightedScalarL2 a) _ d
            (hu.toLp (torusScalarRepresentative U)))) :=
    tendsto_const_nhds.inner
      (angularSourceFreeScalarRadialGraphTest_scalar_L2_tendsto
        ha hU hperiod hu)
  have hsecond :
      Tendsto
        (fun m : ℕ =>
          @inner ℂ (angularWeightedFormL2 a) _ W
            ((angularSourceFreeScalarCutoffGradient_memLp
              hU hperiod hu m).toLp
                (angularSourceFreeScalarCutoffGradient U m)))
        atTop (nhds (0 : ℂ)) := by
    simpa using tendsto_const_nhds.inner
      (angularSourceFreeScalarCutoffGradient_L2_tendsto_zero
        hU hperiod hu)
  have hlimit := hfirst.sub hsecond
  simp only [sub_zero] at hlimit
  apply Filter.Tendsto.congr' _ hlimit
  filter_upwards [] with m
  exact (angularSourceFreeTruncatedGradientL2_resolvent_pairing
    ha hU hperiod hu m g).symm
end Ehrhart.TorusHomogeneousBrascampLieb
