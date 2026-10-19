-- Prove2me | solution 1 for Ehrhart.WeightedTorusBochner.angularTorus_weighted_complex_dolbeault_form_bochner_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/c8c591c5-6fc7-41c8-b84d-30a9b7c761bd

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_sourceTorusFormExterior_add_mixed_eq_full
import Theorems.Thm_Ehrhart_WeightedTorusBochner_angularTorus_weighted_complex_bochner_form_cross_identity
import Theorems.Thm_Ehrhart_WeightedTorusBochner_integrable_angularTorusFormMixedDerivativeDensity
import Theorems.Thm_Ehrhart_WeightedTorusBochner_integrable_angularTorusFormCurvatureDensity
import Theorems.Thm_Ehrhart_WeightedTorusBochner_integrable_angularTorusFormExteriorDerivativeDensity

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
      sourceTorusFormExteriorDerivativeDensity W p
      ∂(angularWeightedTorusMeasure a)) +
    (∫ p : LogTorus n,
      angularTorusFormAdjoint a W p *
        conj (angularTorusFormAdjoint a W p)
      ∂(angularWeightedTorusMeasure a)) =
    (∫ p : LogTorus n,
      sourceTorusFormFullDerivativeDensity W p
      ∂(angularWeightedTorusMeasure a)) +
    (∫ p : LogTorus n,
      angularTorusFormCurvatureDensity a W p
      ∂(angularWeightedTorusMeasure a)) := by
  let T := LogTorus n
  let μ : Measure T := angularWeightedTorusMeasure a
  have hm : Integrable
      (sourceTorusFormMixedDerivativeDensity W) μ :=
    integrable_angularTorusFormMixedDerivativeDensity
      W ha hW hWp hWc
  have hc : Integrable
      (angularTorusFormCurvatureDensity a W) μ :=
    integrable_angularTorusFormCurvatureDensity
      W ha ha2 hW hWp hWc
  have he : Integrable
      (sourceTorusFormExteriorDerivativeDensity W) μ :=
    integrable_angularTorusFormExteriorDerivativeDensity
      W ha hW hWp hWc
  have hcross := angularTorus_weighted_complex_bochner_form_cross_identity
    W ha ha2 hW hWp hWc
  change
    (∫ p : T, sourceTorusFormExteriorDerivativeDensity W p ∂μ) +
      (∫ p : T,
        angularTorusFormAdjoint a W p *
          conj (angularTorusFormAdjoint a W p) ∂μ) =
    (∫ p : T, sourceTorusFormFullDerivativeDensity W p ∂μ) +
      (∫ p : T, angularTorusFormCurvatureDensity a W p ∂μ)
  calc
    _ = (∫ p : T,
        sourceTorusFormExteriorDerivativeDensity W p ∂μ) +
      (∫ p : T,
        (sourceTorusFormMixedDerivativeDensity W p +
          angularTorusFormCurvatureDensity a W p) ∂μ) := by
      rw [hcross]
    _ = ((∫ p : T,
        sourceTorusFormExteriorDerivativeDensity W p ∂μ) +
        (∫ p : T,
          sourceTorusFormMixedDerivativeDensity W p ∂μ)) +
      (∫ p : T,
        angularTorusFormCurvatureDensity a W p ∂μ) := by
      rw [MeasureTheory.integral_add hm hc]
      ring
    _ = (∫ p : T,
        (sourceTorusFormExteriorDerivativeDensity W p +
          sourceTorusFormMixedDerivativeDensity W p) ∂μ) +
      (∫ p : T,
        angularTorusFormCurvatureDensity a W p ∂μ) := by
      rw [MeasureTheory.integral_add he hm]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with p
      exact sourceTorusFormExterior_add_mixed_eq_full W p
end Ehrhart.WeightedTorusBochner
