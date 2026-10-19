-- Prove2me | solution 1 for Ehrhart.WeightedTorusBochner.integrable_angularTorusFormExteriorDerivativeDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/d003e4b1-036d-400b-93ab-4a5a4cd384a7

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_sourceTorusFormExterior_add_mixed_eq_full
import Theorems.Thm_Ehrhart_WeightedTorusBochner_integrable_angularTorusFormMixedDerivativeDensity
import Theorems.Thm_Ehrhart_WeightedTorusBochner_integrable_angularTorusFormFullDerivativeDensity

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
    (hW : ∀ i : Fin n, ContDiff ℝ 2 (fun z => W z i))
    (hWp : ∀ (i : Fin n) (q : Fin n → ℤ),
      Function.Periodic (fun z => W z i)
        (TorusCharacters.imaginaryShift q))
    (hWc : ∀ i : Fin n,
      HasCompactSupport (torusScalarRepresentative (fun z => W z i))) :
    Integrable (sourceTorusFormExteriorDerivativeDensity W)
      (angularWeightedTorusMeasure a) := by
  have hf := integrable_angularTorusFormFullDerivativeDensity
    W ha hW hWp hWc
  have hm := integrable_angularTorusFormMixedDerivativeDensity
    W ha hW hWp hWc
  apply (hf.sub hm).congr
  filter_upwards [] with p
  have hp := sourceTorusFormExterior_add_mixed_eq_full W p
  change
    sourceTorusFormFullDerivativeDensity W p -
      sourceTorusFormMixedDerivativeDensity W p =
        sourceTorusFormExteriorDerivativeDensity W p
  linear_combination -hp
end Ehrhart.WeightedTorusBochner
