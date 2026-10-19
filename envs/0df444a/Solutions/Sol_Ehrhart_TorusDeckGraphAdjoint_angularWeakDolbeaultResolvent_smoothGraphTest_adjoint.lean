-- Prove2me | solution 1 for Ehrhart.TorusDeckGraphAdjoint.angularWeakDolbeaultResolvent_smoothGraphTest_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/318c468b-5af0-4615-91c1-f8b027bf29c5

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusDolbeault_smoothAngularDolbeaultGraph_mem
import Theorems.Thm_Ehrhart_WeightedTorusDolbeault_angularWeakDolbeaultResolvent_form_adjoint

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
    {n : ℕ} (a : LogTorus n → ℝ)
    (f : angularWeightedScalarL2 a)
    (F : TorusCharacters.LogSpace n → ℂ)
    (hFcont : ContDiff ℝ 3 F)
    (hFperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (hFcompact : HasCompactSupport (torusScalarRepresentative F))
    (hF : MemLp (torusScalarRepresentative F) 2
      (angularWeightedTorusMeasure a))
    (hD : MemLp (torusFunctionBarPartialRepresentative F) 2
      (angularWeightedTorusMeasure a)) :
    @inner ℂ (angularWeightedFormL2 a) _
      (WithLp.snd
        (angularWeakDolbeaultResolvent a f :
          angularDolbeaultGraphAmbient a))
      (angularBarPartialL2OfRepresentative a F hD) =
    @inner ℂ (angularWeightedScalarL2 a) _
      (f - angularWeakScalarResolventCLM a f)
      (angularScalarL2OfRepresentative a F hF) := by
  let v : angularDolbeaultGraph a :=
    ⟨WithLp.toLp 2
      (angularScalarL2OfRepresentative a F hF,
       angularBarPartialL2OfRepresentative a F hD),
      smoothAngularDolbeaultGraph_mem
        a F hFcont hFperiod hFcompact hF hD⟩
  exact angularWeakDolbeaultResolvent_form_adjoint a f v
end Ehrhart.TorusDeckGraphAdjoint
