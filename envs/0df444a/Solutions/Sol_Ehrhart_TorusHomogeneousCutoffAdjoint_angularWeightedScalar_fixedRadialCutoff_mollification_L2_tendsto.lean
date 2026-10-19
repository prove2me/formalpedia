-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousCutoffAdjoint.angularWeightedScalar_fixedRadialCutoff_mollification_L2_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/430babdb-cb13-445b-8818-d788aaa21f51

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusStrongWeightedRadialCutoff_angularWeightedLp_tendsto_of_squared_error_integral
import Theorems.Thm_Ehrhart_TorusHomogeneousCutoffAdjoint_angularWeightedScalar_fixedRadialCutoff_mollification_integral_tendsto_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusHomogeneousCutoffAdjoint
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert
open ComplexKillingSaturationBridge WeightedTorusDistributionBridge WeightedDolbeaultBochnerIdentity
open MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation MatrixTorusBochnerIdentity
open WeightedTorusDolbeault TorusWeakDolbeaultMollification TorusMollifiedBochner
open TorusFriedrichsMollifierEstimates TorusWeightedAdjointMollification
open TorusStrongWeightedTorusDescent TorusStrongWeightedRadialCutoff TorusFriedrichsCutoff
open BergmanJetStrictMixedLocalCore
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusHomogeneousCutoffAdjoint
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (f : angularWeightedScalarL2 a) (m : ℕ) :
    Tendsto
      (fun k : ℕ =>
        (angularWeightedScalar_fixedRadialCutoff_mollification_memLp
          ha f m k).toLp
          (fun q : LogTorus n =>
            (sourceRadialCutoff m q : ℂ) •
              torusScalarRepresentative
                (normalizedCoverMollification
                  (complexTorusCoverLift
                    (fun r : LogTorus n => f r)) k) q))
      atTop
      (nhds
        ((angularSourceRadialCutoff_smul_memLp
          (MeasureTheory.Lp.memLp f) m).toLp
          (fun q : LogTorus n =>
            (sourceRadialCutoff m q : ℂ) • f q))) := by
  apply angularWeightedLp_tendsto_of_squared_error_integral
    (fun k => angularWeightedScalar_fixedRadialCutoff_mollification_memLp
      ha f m k)
    (angularSourceRadialCutoff_smul_memLp
      (MeasureTheory.Lp.memLp f) m)
  exact angularWeightedScalar_fixedRadialCutoff_mollification_integral_tendsto_zero
    ha f m
end Ehrhart.TorusHomogeneousCutoffAdjoint
