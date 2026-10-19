-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerCoreApproximation.sourceTorusBarPartial_cutoffPhysicalField
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/1cc07df6-bb1e-4aad-af64-5db0992c59c8

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_barPartialCoordinate_mul
import Theorems.Thm_Ehrhart_MatrixTorusBochnerCoreApproximation_torusScalarRepresentative_add

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MatrixTorusBochnerCoreApproximation
open Set Function MeasureTheory Filter Matrix
open EqualitySaturatingKillingPaths ComplexKillingSaturationBridge MatrixTorusBochnerIdentity
open MatrixTorusBochnerCore MatrixTorusBochnerCoreDensity WeightedResolventConstantCore
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.MatrixTorusBochnerCoreApproximation
theorem _root_.solution
    {n : ℕ} (m : ℕ)
    {W : TorusCharacters.LogSpace n →
      TorusCharacters.LogSpace n}
    (hW : ContDiff ℝ 2 W)
    (i j : Fin n)
    (p : WeightedTorusHilbert.LogTorus n) :
    sourceTorusBarPartial
      (fun z => cutoffPhysicalField m W z i) j p =
      (sourceRadialCutoff m p : ℂ) *
        sourceTorusBarPartial (fun z => W z i) j p +
      torusScalarRepresentative (fun z => W z i) p *
        sourceTorusBarPartial
          (complexSourceCoverRadialCutoff m) j p := by
  have hproduct :
      (fun z : TorusCharacters.LogSpace n =>
        barPartialCoordinate
          (fun w => complexSourceCoverRadialCutoff m w * W w i)
          z j) =
      (fun z : TorusCharacters.LogSpace n =>
        complexSourceCoverRadialCutoff m z *
          barPartialCoordinate (fun w => W w i) z j +
        W z i * barPartialCoordinate
          (complexSourceCoverRadialCutoff m) z j) := by
    funext z
    exact barPartialCoordinate_mul
      ((contDiff_complexSourceCoverRadialCutoff m).differentiable
        (by norm_num))
      ((contDiff_pi.mp hW i).differentiable
        (by norm_num)) z j
  unfold sourceTorusBarPartial
  change
    torusScalarRepresentative
      (fun z => barPartialCoordinate
        (fun w => complexSourceCoverRadialCutoff m w * W w i)
        z j) p = _
  rw [hproduct, torusScalarRepresentative_add,
    torusScalarRepresentative_mul,
    torusScalarRepresentative_mul,
    torusScalarRepresentative_complexSourceCoverRadialCutoff]
end Ehrhart.MatrixTorusBochnerCoreApproximation
