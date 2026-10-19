-- Prove2me | solution 1 for Ehrhart.TorusDeckGraphAdjoint.angularWeakDolbeaultResolvent_smoothGraphTest_adjoint_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/3f5e07d2-680e-4b10-a6eb-a253fe005916

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusDeckGraphAdjoint_angularWeakDolbeaultResolvent_smoothGraphTest_adjoint

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
    (∫ q : LogTorus n,
      @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        ((WithLp.snd
          (angularWeakDolbeaultResolvent a f :
            angularDolbeaultGraphAmbient a)) q)
        (torusFunctionBarPartialRepresentative F q)
      ∂(angularWeightedTorusMeasure a)) =
    (∫ q : LogTorus n,
      @inner ℂ ℂ _
        ((f - angularWeakScalarResolventCLM a f) q)
        (torusScalarRepresentative F q)
      ∂(angularWeightedTorusMeasure a)) := by
  have h := angularWeakDolbeaultResolvent_smoothGraphTest_adjoint
    a f F hFcont hFperiod hFcompact hF hD
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def] at h
  calc
    (∫ q : LogTorus n,
      @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        ((WithLp.snd
          (angularWeakDolbeaultResolvent a f :
            angularDolbeaultGraphAmbient a)) q)
        (torusFunctionBarPartialRepresentative F q)
      ∂(angularWeightedTorusMeasure a)) =
      ∫ q : LogTorus n,
        @inner ℂ (EuclideanSpace ℂ (Fin n)) _
          ((WithLp.snd
            (angularWeakDolbeaultResolvent a f :
              angularDolbeaultGraphAmbient a)) q)
          ((angularBarPartialL2OfRepresentative a F hD) q)
        ∂(angularWeightedTorusMeasure a) := by
      apply integral_congr_ae
      filter_upwards [hD.coeFn_toLp] with q hq
      unfold angularBarPartialL2OfRepresentative
      rw [hq]
    _ = ∫ q : LogTorus n,
        @inner ℂ ℂ _
          ((f - angularWeakScalarResolventCLM a f) q)
          ((angularScalarL2OfRepresentative a F hF) q)
        ∂(angularWeightedTorusMeasure a) := h
    _ = ∫ q : LogTorus n,
        @inner ℂ ℂ _
          ((f - angularWeakScalarResolventCLM a f) q)
          (torusScalarRepresentative F q)
        ∂(angularWeightedTorusMeasure a) := by
      apply integral_congr_ae
      filter_upwards [hF.coeFn_toLp] with q hq
      unfold angularScalarL2OfRepresentative
      rw [hq]
end Ehrhart.TorusDeckGraphAdjoint
