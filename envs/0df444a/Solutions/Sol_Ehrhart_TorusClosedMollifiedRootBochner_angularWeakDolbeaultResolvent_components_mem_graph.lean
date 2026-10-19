-- Prove2me | solution 1 for Ehrhart.TorusClosedMollifiedRootBochner.angularWeakDolbeaultResolvent_components_mem_graph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/080b6464-dc3c-435a-baf5-3c0894efb8f0

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
    (g : angularWeightedScalarL2 a) :
    WithLp.toLp 2
      (angularWeakScalarResolventCLM a g,
       WithLp.snd
        (angularWeakDolbeaultResolvent a g :
          angularDolbeaultGraphAmbient a)) ∈
      angularDolbeaultGraph a := by
  have h := (angularWeakDolbeaultResolvent a g).property
  rw [angularWeakScalarResolventCLM_apply]
  change WithLp.toLp 2
    ((angularWeakDolbeaultResolvent a g :
      angularDolbeaultGraphAmbient a).ofLp) ∈
    angularDolbeaultGraph a
  rw [WithLp.toLp_ofLp]
  exact h
end Ehrhart.TorusClosedMollifiedRootBochner
