-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousSmoothRootBochner.angularWeakResolventClosedMollifiedRootBochner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/0f97cff4-b8a3-407d-ac53-e3ffe03d1c57

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusClosedMollifiedRootBochner_angularWeakDolbeaultResolvent_components_mem_graph
import Theorems.Thm_Ehrhart_TorusHomogeneousSmoothRootBochner_angularClosedGraphMollifiedRootBochner

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusHomogeneousSmoothRootBochner
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert EqualitySaturatingKillingPaths
open MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence MatrixTorusBochnerIdentity WeightedTorusDolbeault
open WeightedTorusBochner WeightedTorusBrascampLieb MatrixTorusDolbeaultGraph
open RadialPhysicalInverseSquareRootEnergy TorusRootCurvatureCoercivity TorusNoncompactBochner
open RadialPhysicalResolventRootCutoffPairing TorusMollifiedBochner TorusWeakRadialExteriorEnergy
open TorusClosedMollifiedRootBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder ComplexOrder Matrix.Norms.L2Operator Topology ContDiff
namespace Ehrhart.TorusHomogeneousSmoothRootBochner
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (g : angularWeightedScalarL2 a)
    (ℓ m : ℕ) :
    let W : angularWeightedFormL2 a :=
      WithLp.snd
        (angularWeakDolbeaultResolvent a g :
          angularDolbeaultGraphAmbient a)
    ‖angularClosedMollifiedRootVectorL2
      ha ha2 hH W ℓ m‖ ^ 2 ≤
    (∫ q : LogTorus n,
      angularTorusFormAdjoint a
        (cutoffPhysicalField m
          (angularGraphMollifiedPhysicalField W ℓ)) q *
      conj (angularTorusFormAdjoint a
        (cutoffPhysicalField m
          (angularGraphMollifiedPhysicalField W ℓ)) q)
      ∂(angularWeightedTorusMeasure a)).re +
    (∫ q : LogTorus n,
      complexEuclideanAntisymmetricEnergy
        (sourceCutoffDerivativeCommutator m
          (angularGraphMollifiedPhysicalField W ℓ) q)
      ∂(angularWeightedTorusMeasure a)).re := by
  dsimp only
  exact angularClosedGraphMollifiedRootBochner
    ha ha2 hH (angularWeakScalarResolventCLM a g)
    (WithLp.snd
      (angularWeakDolbeaultResolvent a g :
        angularDolbeaultGraphAmbient a))
    (angularWeakDolbeaultResolvent_components_mem_graph a g)
    ℓ m
end Ehrhart.TorusHomogeneousSmoothRootBochner
