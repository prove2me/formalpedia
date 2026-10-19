-- Prove2me | solution 1 for Ehrhart.WeightedTorusBochner.integral_angularTorusFormMixed_add_curvature_eq_coordinate_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/9e09d027-5fb4-4721-9a44-d3bd77fd6f88

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusBochner_integrable_angularTorusBarPartial_pair
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
    (∫ p : LogTorus n,
      sourceTorusFormMixedDerivativeDensity W p +
        angularTorusFormCurvatureDensity a W p
      ∂(angularWeightedTorusMeasure a)) =
    ∑ i : Fin n, ∑ j : Fin n,
      ∫ p : LogTorus n,
        (sourceTorusBarPartial (fun z => W z i) j p *
          conj (sourceTorusBarPartial (fun z => W z j) i p) +
          (torusScalarRepresentative (fun z => W z i) p *
            angularTorusComplexHessian a i j p) *
              conj (torusScalarRepresentative (fun z => W z j) p))
        ∂(angularWeightedTorusMeasure a) := by
  let T := LogTorus n
  let μ : Measure T := angularWeightedTorusMeasure a
  have hp (i j : Fin n) : Integrable
      (fun p : T =>
        sourceTorusBarPartial (fun z => W z i) j p *
          conj (sourceTorusBarPartial (fun z => W z j) i p) +
          (torusScalarRepresentative (fun z => W z i) p *
            angularTorusComplexHessian a i j p) *
              conj (torusScalarRepresentative (fun z => W z j) p)) μ :=
    (integrable_angularTorusBarPartial_pair
      ha (hW i) (hW j)
      (hWp i) (hWp j) (hWc j) j i).add
        (integrable_angularTorusComplexHessian_pair
          ha ha2 (hW i) (hW j)
          (hWp i) (hWp j) (hWc j) i j)
  change
    (∫ p : T,
      sourceTorusFormMixedDerivativeDensity W p +
        angularTorusFormCurvatureDensity a W p ∂μ) =
    ∑ i : Fin n, ∑ j : Fin n,
      ∫ p : T,
        (sourceTorusBarPartial (fun z => W z i) j p *
          conj (sourceTorusBarPartial (fun z => W z j) i p) +
          (torusScalarRepresentative (fun z => W z i) p *
            angularTorusComplexHessian a i j p) *
              conj (torusScalarRepresentative (fun z => W z j) p)) ∂μ
  calc
    _ = ∫ p : T, ∑ i : Fin n, ∑ j : Fin n,
      (sourceTorusBarPartial (fun z => W z i) j p *
        conj (sourceTorusBarPartial (fun z => W z j) i p) +
        (torusScalarRepresentative (fun z => W z i) p *
          angularTorusComplexHessian a i j p) *
            conj (torusScalarRepresentative (fun z => W z j) p)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with p
      simp only [sourceTorusFormMixedDerivativeDensity,
        angularTorusFormCurvatureDensity, ← Finset.sum_add_distrib]
    _ = ∑ i : Fin n,
      ∫ p : T, ∑ j : Fin n,
        (sourceTorusBarPartial (fun z => W z i) j p *
          conj (sourceTorusBarPartial (fun z => W z j) i p) +
          (torusScalarRepresentative (fun z => W z i) p *
            angularTorusComplexHessian a i j p) *
              conj (torusScalarRepresentative (fun z => W z j) p)) ∂μ := by
      exact MeasureTheory.integral_finsetSum Finset.univ
        (fun i _ => MeasureTheory.integrable_finsetSum Finset.univ
          (fun j _ => hp i j))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact MeasureTheory.integral_finsetSum Finset.univ
        (fun j _ => hp i j)
end Ehrhart.WeightedTorusBochner
