-- Prove2me | solution 1 for Ehrhart.JetEnvelopeLocalGrowth.sourcePositiveAngularArc_haarMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/510c9ddd-8c03-4946-9805-f1471b315216

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JetEnvelopeLocalGrowth_sourceUnitAngularHaar_eq_volume
import Theorems.Thm_Ehrhart_JetEnvelopeLocalGrowth_measurableSet_sourcePositiveAngularArc

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.JetEnvelopeLocalGrowth
open Set Filter MeasureTheory Module Metric Asymptotics
open ActualJetUpperEnvelope JetEnvelopeSlopeConvergence JetEnvelopeRightDerivative
open scoped BigOperators Topology ENNReal InnerProductSpace
universe u v
namespace Ehrhart.JetEnvelopeLocalGrowth
theorem _root_.solution
    {δ : ℝ} (hδ : δ ≤ 1) :
    AddCircle.haarAddCircle (sourcePositiveAngularArc δ) =
      ENNReal.ofReal δ := by
  rw [sourceUnitAngularHaar_eq_volume]
  rw [AddCircle.add_projection_respects_measure 1 0
    (measurableSet_sourcePositiveAngularArc δ)]
  have hset :
      (QuotientAddGroup.mk ⁻¹' sourcePositiveAngularArc δ ∩
        Set.Ioc (0 : ℝ) (0 + 1)) = Set.Ioo (0 : ℝ) δ := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨harc, hinter⟩
      have hrepr := AddCircle.equivIoc_coe_eq hinter
      change
        ((AddCircle.equivIoc 1 0 (x : UnitAddCircle)).1 : ℝ) < δ
        at harc
      rw [hrepr] at harc
      exact ⟨hinter.1, harc⟩
    · intro hx
      have hinter : x ∈ Set.Ioc (0 : ℝ) (0 + 1) := by
        constructor
        · exact hx.1
        · linarith [hx.2]
      refine ⟨?_, hinter⟩
      change
        ((AddCircle.equivIoc 1 0 (x : UnitAddCircle)).1 : ℝ) < δ
      rw [AddCircle.equivIoc_coe_eq hinter]
      exact hx.2
  rw [hset, Real.volume_Ioo]
  simp
end Ehrhart.JetEnvelopeLocalGrowth
