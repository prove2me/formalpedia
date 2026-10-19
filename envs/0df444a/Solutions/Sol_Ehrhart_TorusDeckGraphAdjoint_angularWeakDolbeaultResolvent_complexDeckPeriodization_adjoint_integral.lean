-- Prove2me | solution 1 for Ehrhart.TorusDeckGraphAdjoint.angularWeakDolbeaultResolvent_complexDeckPeriodization_adjoint_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/9745adba-6b45-44af-bc22-6cc224a2ca80

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusDeckPeriodization_complexDeckPeriodization_periodic
import Theorems.Thm_Ehrhart_TorusDeckPeriodization_contDiff_complexDeckPeriodization
import Theorems.Thm_Ehrhart_TorusDeckCompactSupport_hasCompactSupport_torusScalarRepresentative_complexDeckPeriodization
import Theorems.Thm_Ehrhart_TorusDeckGraphAdjoint_complexDeckPeriodization_scalar_memLp
import Theorems.Thm_Ehrhart_TorusDeckGraphAdjoint_complexDeckPeriodization_barPartial_memLp
import Theorems.Thm_Ehrhart_TorusDeckGraphAdjoint_angularWeakDolbeaultResolvent_smoothGraphTest_adjoint_integral

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
    (f : angularWeightedScalarL2 a)
    {ψ : TorusCharacters.LogSpace n → ℂ}
    (hψ : ContDiff ℝ 3 ψ)
    (hψcompact : HasCompactSupport ψ) :
    (∫ q : LogTorus n,
      @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        ((WithLp.snd
          (angularWeakDolbeaultResolvent a f :
            angularDolbeaultGraphAmbient a)) q)
        (torusFunctionBarPartialRepresentative
          (complexDeckPeriodization ψ) q)
      ∂(angularWeightedTorusMeasure a)) =
    (∫ q : LogTorus n,
      @inner ℂ ℂ _
        ((f - angularWeakScalarResolventCLM a f) q)
        (torusScalarRepresentative
          (complexDeckPeriodization ψ) q)
      ∂(angularWeightedTorusMeasure a)) := by
  exact angularWeakDolbeaultResolvent_smoothGraphTest_adjoint_integral
    a f (complexDeckPeriodization ψ)
    (contDiff_complexDeckPeriodization hψ hψcompact)
    (fun q => complexDeckPeriodization_periodic ψ q)
    (hasCompactSupport_torusScalarRepresentative_complexDeckPeriodization
      hψcompact)
    (complexDeckPeriodization_scalar_memLp ha hψ hψcompact)
    (complexDeckPeriodization_barPartial_memLp ha hψ hψcompact)
end Ehrhart.TorusDeckGraphAdjoint
