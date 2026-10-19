-- Prove2me | solution 1 for Ehrhart.TorusClosedMollifiedRootBochner.angularTorusFormAdjoint_eq_coverFormAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/724b8dd2-e9f2-425c-ad72-5cc5d60adc52

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusClosedMollifiedRootBochner
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeRightDerivative
open WeightedDolbeaultBochnerIdentity MatrixTorusBochnerIdentity MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault WeightedTorusBochner
open WeightedTorusBrascampLieb TorusNoncompactBochner TorusWeakRadialExteriorEnergy
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace Topology ContDiff
namespace Ehrhart.TorusClosedMollifiedRootBochner
theorem _root_.solution
    {n : ℕ} (a : LogTorus n → ℝ)
    (V : LogSpace n → LogSpace n) (q : LogTorus n) :
    angularTorusFormAdjoint a V q =
      coverFormAdjoint (angularCoverPotential a) V
        (sourceTorusCoverPoint q) := by
  rfl
end Ehrhart.TorusClosedMollifiedRootBochner
