-- Prove2me | solution 1 for Ehrhart.WeightedTorusBochner.angularTorus_weighted_complex_bochner_form_cross_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/50f255e2-9721-46b6-8956-ad6e056e3433

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusBochner_angularTorus_weighted_complex_bochner_form_coordinate_sum
import Theorems.Thm_Ehrhart_WeightedTorusBochner_integral_angularTorusFormAdjoint_mul_conj_eq_coordinate_sum
import Theorems.Thm_Ehrhart_WeightedTorusBochner_integral_angularTorusFormMixed_add_curvature_eq_coordinate_sum

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
    (∫ p : LogTorus n,
      angularTorusFormAdjoint a W p *
        conj (angularTorusFormAdjoint a W p)
      ∂(angularWeightedTorusMeasure a)) =
    ∫ p : LogTorus n,
      (sourceTorusFormMixedDerivativeDensity W p +
        angularTorusFormCurvatureDensity a W p)
      ∂(angularWeightedTorusMeasure a) := by
  calc
    _ = ∑ i : Fin n, ∑ j : Fin n,
      ∫ p : LogTorus n,
        angularTorusWeightedHolomorphicDerivative a
          (fun z => W z i) i p *
          conj (angularTorusWeightedHolomorphicDerivative a
            (fun z => W z j) j p)
        ∂(angularWeightedTorusMeasure a) :=
      integral_angularTorusFormAdjoint_mul_conj_eq_coordinate_sum
        W ha ha2 hW hWp hWc
    _ = ∑ i : Fin n, ∑ j : Fin n,
      ∫ p : LogTorus n,
        (sourceTorusBarPartial (fun z => W z i) j p *
          conj (sourceTorusBarPartial (fun z => W z j) i p) +
          (torusScalarRepresentative (fun z => W z i) p *
            angularTorusComplexHessian a i j p) *
              conj (torusScalarRepresentative (fun z => W z j) p))
        ∂(angularWeightedTorusMeasure a) :=
      angularTorus_weighted_complex_bochner_form_coordinate_sum
        W ha ha2 hW hWp hWc
    _ = _ :=
      (integral_angularTorusFormMixed_add_curvature_eq_coordinate_sum
        W ha ha2 hW hWp hWc).symm
end Ehrhart.WeightedTorusBochner
