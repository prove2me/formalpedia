-- Prove2me | solution 1 for Ehrhart.BergmanJetStrictMixedLocalCore.angularMemLp_normSquared_locallyIntegrable_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/f0cea62d-e435-48e2-8e9f-eed74a82033b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetStrictMixedLocalCore_angularMemLp_restrict_base_isCompact

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetStrictMixedLocalCore
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence
open WeightedTorusDistributionBridge WeightedTorusVectorClosedGraphWeakBridge WeightedTorusDolbeault
open scoped BigOperators ENNReal InnerProductSpace Topology
namespace Ehrhart.BergmanJetStrictMixedLocalCore
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    {g : LogTorus n → ℂ}
    (hg : MemLp g 2 (angularWeightedTorusMeasure a)) :
    LocallyIntegrable
      (fun q : LogTorus n => ((‖g q‖ ^ 2 : ℝ) : ℂ))
      (sourceTorusBaseMeasure n) := by
  apply locallyIntegrable_iff.mpr
  intro S hS
  have hgS := angularMemLp_restrict_base_isCompact ha hg hS
  have hsq :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm
      hgS.aestronglyMeasurable).mp hgS
  exact hsq.ofReal (𝕜 := ℂ)
end Ehrhart.BergmanJetStrictMixedLocalCore
