-- Prove2me | solution 1 for Ehrhart.WeightedTorusBochner.integrable_angularTorusFormCurvatureDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/0e4554cc-0819-4b2d-8d87-bf259f6fc9f4

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusBochner_integrable_angularTorusComplexHessian_pair

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusBochner
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert JetEnvelopeSlopeConvergence EqualitySaturatingKillingPaths
open ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity WeightedTorusDistributionBridge
open WeightedTorusGraphWeakBridge MatrixTorusBochnerBridge MatrixTorusBochnerIdentity
open WeightedTorusDolbeault
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.WeightedTorusBochner
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : TorusCharacters.LogSpace n → Fin n → ℂ)
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hW : ∀ i : Fin n, ContDiff ℝ 2 (fun z => W z i))
    (hWp : ∀ (i : Fin n) (q : Fin n → ℤ),
      Function.Periodic (fun z => W z i)
        (TorusCharacters.imaginaryShift q))
    (hWc : ∀ i : Fin n,
      HasCompactSupport (torusScalarRepresentative (fun z => W z i))) :
    Integrable (angularTorusFormCurvatureDensity a W)
      (angularWeightedTorusMeasure a) := by
  unfold angularTorusFormCurvatureDensity
  exact MeasureTheory.integrable_finsetSum Finset.univ
    (fun i _ => MeasureTheory.integrable_finsetSum Finset.univ
      (fun j _ => integrable_angularTorusComplexHessian_pair
        ha ha2 (hW i) (hW j)
        (hWp i) (hWp j) (hWc j) i j))
end Ehrhart.WeightedTorusBochner
