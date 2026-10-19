-- Prove2me | solution 1 for Ehrhart.WeightedTorusBrascampLieb.angularWeakScalarResolventCLM_fixed_iff_graph_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/fbf248ef-c363-4ab4-9339-c66b1cb74da2

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusDolbeault_angularWeakDolbeaultResolvent_moment_components

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusBrascampLieb
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert WeightedBrascampSaturation ComplexKillingSaturationBridge
open ComplexSaturatedKillingFieldBridge WeightedTorusWeylWeakRepresentativeBridge
open JointHolomorphicLaurentFourierCompatibility WeightedTorusDolbeault WeightedTorusBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.WeightedTorusBrascampLieb
theorem _root_.solution
    {n : ℕ} (a : LogTorus n → ℝ)
    (f : angularWeightedScalarL2 a) :
    angularWeakScalarResolventCLM a f = f ↔
      WithLp.toLp 2 (f, (0 : angularWeightedFormL2 a)) ∈
        angularDolbeaultGraph a := by
  constructor
  · intro hfixed
    have hscalar :
        WithLp.fst (angularWeakDolbeaultResolvent a f :
          angularDolbeaultGraphAmbient a) = f := by
      simpa only [angularWeakScalarResolventCLM_apply] using hfixed
    have hvar := angularWeakDolbeaultResolvent_moment_components
      a f (angularWeakDolbeaultResolvent a f)
    rw [hscalar] at hvar
    have hinner :
        @inner ℂ (angularWeightedFormL2 a) _
          (WithLp.snd (angularWeakDolbeaultResolvent a f :
            angularDolbeaultGraphAmbient a))
          (WithLp.snd (angularWeakDolbeaultResolvent a f :
            angularDolbeaultGraphAmbient a)) = 0 := by
      linear_combination hvar
    have hgradient :
        WithLp.snd (angularWeakDolbeaultResolvent a f :
          angularDolbeaultGraphAmbient a) = 0 :=
      (inner_self_eq_zero).mp hinner
    have hpair :
        (angularWeakDolbeaultResolvent a f :
          angularDolbeaultGraphAmbient a) =
            WithLp.toLp 2 (f, (0 : angularWeightedFormL2 a)) := by
      apply (WithLp.prodContinuousLinearEquiv 2 ℂ
        (angularWeightedScalarL2 a)
        (angularWeightedFormL2 a)).injective
      exact Prod.ext hscalar hgradient
    rw [← hpair]
    exact (angularWeakDolbeaultResolvent a f).property
  · intro hgraph
    have hproj :=
      (angularDolbeaultGraph a).starProjection_eq_self_iff.mpr hgraph
    change WithLp.fst
      ((angularDolbeaultGraph a).starProjection
        (WithLp.toLp 2 (f, (0 : angularWeightedFormL2 a)))) = f
    rw [hproj]
    rfl
end Ehrhart.WeightedTorusBrascampLieb
