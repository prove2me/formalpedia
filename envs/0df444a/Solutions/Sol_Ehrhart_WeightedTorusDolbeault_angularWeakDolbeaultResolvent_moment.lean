-- Prove2me | solution 1 for Ehrhart.WeightedTorusDolbeault.angularWeakDolbeaultResolvent_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/286ba929-ca2e-4bdf-8e7e-c04d9865128d

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusDolbeault
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert JetEnvelopeSlopeConvergence ComplexKillingSaturationBridge
open WeightedTorusDistributionBridge MatrixTorusBochnerIdentity
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.WeightedTorusDolbeault
theorem _root_.solution {n : ℕ}
    (a : LogTorus n → ℝ)
    (f : angularWeightedScalarL2 a)
    (v : angularDolbeaultGraph a) :
    @inner ℂ (angularDolbeaultGraphAmbient a) _
      (WithLp.toLp 2 (f, (0 : angularWeightedFormL2 a)) -
        (angularWeakDolbeaultResolvent a f :
          angularDolbeaultGraphAmbient a))
      (v : angularDolbeaultGraphAmbient a) = 0 := by
  exact (angularDolbeaultGraph a).starProjection_inner_eq_zero
    (WithLp.toLp 2 (f, (0 : angularWeightedFormL2 a)))
    (v : angularDolbeaultGraphAmbient a) v.property
end Ehrhart.WeightedTorusDolbeault
