-- Prove2me | solution 1 for Ehrhart.TorusNoncompactBochner.sourceTorusBarPartial_cutoffPhysicalField_antisymmetric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/5436e60e-130a-4c60-a8a5-83e115fb7676

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerCoreApproximation_sourceTorusBarPartial_cutoffPhysicalField

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusNoncompactBochner
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert TorusCharacters ComplexKillingSaturationBridge MatrixTorusBochnerIdentity
open MatrixTorusBochnerCore MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault WeightedTorusBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.TorusNoncompactBochner
theorem _root_.solution
    {n : ℕ}
    {W : LogSpace n → LogSpace n}
    (hW : ContDiff ℝ 2 W)
    (hclosed : ∀ q : LogTorus n,
      Matrix.IsSymm (fun i j : Fin n =>
        sourceTorusBarPartial (fun z => W z i) j q))
    (m : ℕ) (i j : Fin n) (p : LogTorus n) :
    sourceTorusBarPartial
        (fun z => cutoffPhysicalField m W z i) j p -
      sourceTorusBarPartial
        (fun z => cutoffPhysicalField m W z j) i p =
      sourceCutoffDerivativeCommutator m W p (i, j) -
        sourceCutoffDerivativeCommutator m W p (j, i) := by
  rw [sourceTorusBarPartial_cutoffPhysicalField m hW i j p,
    sourceTorusBarPartial_cutoffPhysicalField m hW j i p,
    (hclosed p).apply j i]
  change
    ((sourceRadialCutoff m p : ℂ) *
        sourceTorusBarPartial (fun z => W z j) i p +
      torusScalarRepresentative (fun z => W z i) p *
        sourceTorusBarPartial (complexSourceCoverRadialCutoff m) j p) -
      ((sourceRadialCutoff m p : ℂ) *
        sourceTorusBarPartial (fun z => W z j) i p +
      torusScalarRepresentative (fun z => W z j) p *
        sourceTorusBarPartial (complexSourceCoverRadialCutoff m) i p) =
      torusScalarRepresentative (fun z => W z i) p *
        sourceTorusBarPartial (complexSourceCoverRadialCutoff m) j p -
      torusScalarRepresentative (fun z => W z j) p *
        sourceTorusBarPartial (complexSourceCoverRadialCutoff m) i p
  ring
end Ehrhart.TorusNoncompactBochner
