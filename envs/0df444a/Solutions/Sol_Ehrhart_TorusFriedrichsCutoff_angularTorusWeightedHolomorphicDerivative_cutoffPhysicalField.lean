-- Prove2me | solution 1 for Ehrhart.TorusFriedrichsCutoff.angularTorusWeightedHolomorphicDerivative_cutoffPhysicalField
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/1f216801-1d27-49b3-be40-0d648a67587c

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_weightedHolomorphicDerivative_mul
import Theorems.Thm_Ehrhart_MatrixTorusBochnerCoreApproximation_torusScalarRepresentative_add

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
    {n : ℕ} (a : LogTorus n → ℝ) (m : ℕ)
    {W : LogSpace n → LogSpace n}
    (hW : ContDiff ℝ 2 W)
    (i : Fin n) (q : LogTorus n) :
    angularTorusWeightedHolomorphicDerivative a
      (fun z => cutoffPhysicalField m W z i) i q =
      (sourceRadialCutoff m q : ℂ) *
        angularTorusWeightedHolomorphicDerivative a
          (fun z => W z i) i q +
      torusScalarRepresentative (fun z => W z i) q *
        torusScalarRepresentative
          (fun z => holomorphicCoordinate
            (complexSourceCoverRadialCutoff m) z i) q := by
  have hproduct :
      (fun z : LogSpace n =>
        weightedHolomorphicDerivative (angularCoverPotential a)
          (fun w => complexSourceCoverRadialCutoff m w * W w i)
            i z) =
      (fun z : LogSpace n =>
        complexSourceCoverRadialCutoff m z *
          weightedHolomorphicDerivative
            (angularCoverPotential a) (fun w => W w i) i z +
        W z i *
          holomorphicCoordinate (complexSourceCoverRadialCutoff m) z i) := by
    funext z
    exact weightedHolomorphicDerivative_mul
      (angularCoverPotential a)
      ((contDiff_complexSourceCoverRadialCutoff m).differentiable
        (by norm_num))
      ((contDiff_pi.mp hW i).differentiable
        (by norm_num)) z i
  unfold angularTorusWeightedHolomorphicDerivative
  change
    torusScalarRepresentative
      (fun z => weightedHolomorphicDerivative
        (angularCoverPotential a)
        (fun w => complexSourceCoverRadialCutoff m w * W w i)
          i z) q = _
  rw [hproduct, torusScalarRepresentative_add,
    torusScalarRepresentative_mul,
    torusScalarRepresentative_mul,
    torusScalarRepresentative_complexSourceCoverRadialCutoff]
end Ehrhart.TorusFriedrichsCutoff
