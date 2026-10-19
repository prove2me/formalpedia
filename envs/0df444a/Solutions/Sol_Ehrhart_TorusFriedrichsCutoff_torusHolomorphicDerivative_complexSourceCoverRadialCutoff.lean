-- Prove2me | solution 1 for Ehrhart.TorusFriedrichsCutoff.torusHolomorphicDerivative_complexSourceCoverRadialCutoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/0910cf44-f4b1-4665-b2c3-87bcc9292b35

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusFriedrichsCutoff
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert TorusCharacters JetEnvelopeRightDerivative EqualitySaturatingKillingPaths
open ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity MatrixTorusBochnerIdentity
open MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault WeightedTorusBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff
namespace Ehrhart.TorusFriedrichsCutoff
theorem _root_.solution
    {n : ℕ} (m : ℕ) (i : Fin n) (q : LogTorus n) :
    torusScalarRepresentative
      (fun z => holomorphicCoordinate
        (complexSourceCoverRadialCutoff m) z i) q =
      conj (sourceTorusBarPartial
        (complexSourceCoverRadialCutoff m) i q) := by
  change
    holomorphicCoordinate
      (fun z => (sourceCoverRadialCutoff m z : ℂ))
        (sourceTorusCoverPoint q) i =
      conj (barPartialCoordinate
        (fun z => (sourceCoverRadialCutoff m z : ℂ))
          (sourceTorusCoverPoint q) i)
  exact (conj_barPartialCoordinate_real
    ((contDiff_sourceCoverRadialCutoff m).differentiable
      (by norm_num)) (sourceTorusCoverPoint q) i).symm
end Ehrhart.TorusFriedrichsCutoff
