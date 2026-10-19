-- Prove2me | solution 1 for Ehrhart.TorusDeckGraphAdjoint.complexDeckPeriodization_barPartial_memLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/6b678217-3364-459f-9d39-450bd0543067

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusDeckPeriodization_complexDeckPeriodization_periodic
import Theorems.Thm_Ehrhart_TorusDeckPeriodization_contDiff_complexDeckPeriodization
import Theorems.Thm_Ehrhart_TorusDeckCompactSupport_hasCompactSupport_torusScalarRepresentative_complexDeckPeriodization

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusDeckGraphAdjoint
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert ComplexKillingSaturationBridge MatrixTorusBochnerIdentity
open WeightedTorusDolbeault WeightedTorusBrascampLieb TorusDeckPeriodization TorusDeckCompactSupport
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusDeckGraphAdjoint
theorem _root_.solution
    {n : ℕ}
    {a : LogTorus n → ℝ}
    (ha : Continuous a)
    {ψ : TorusCharacters.LogSpace n → ℂ}
    (hψ : ContDiff ℝ 3 ψ)
    (hψcompact : HasCompactSupport ψ) :
    MemLp
      (torusFunctionBarPartialRepresentative
        (complexDeckPeriodization ψ)) 2
      (angularWeightedTorusMeasure a) := by
  let : IsLocallyFiniteMeasure (angularWeightedTorusMeasure a) :=
    angularWeightedTorusMeasure_isLocallyFinite ha
  apply
    (continuous_torusFunctionBarPartialRepresentative_of_periodic
      ((contDiff_complexDeckPeriodization hψ hψcompact).of_le
        (by norm_num))
      (fun q => complexDeckPeriodization_periodic ψ q)).memLp_of_hasCompactSupport
  exact
    hasCompactSupport_torusFunctionBarPartialRepresentative_of_periodic
      (complexDeckPeriodization ψ)
      (fun q => complexDeckPeriodization_periodic ψ q)
      (hasCompactSupport_torusScalarRepresentative_complexDeckPeriodization
        hψcompact)
end Ehrhart.TorusDeckGraphAdjoint
