-- Prove2me | solution 1 for Ehrhart.ComplexSaturatedKillingFieldBridge.realFundamentalEmbedding_measurePreserving
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/cbff37c7-7576-432c-8a9a-208cf31f5e8d

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusDistributionBridge_angularFundamentalEquiv_measurePreserving
import Theorems.Thm_Ehrhart_ComplexSaturatedKillingFieldBridge_angularFundamentalCell_set_measurable

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.ComplexSaturatedKillingFieldBridge
open Set Function MeasureTheory Filter
open scoped BigOperators ContDiff Convolution ENNReal InnerProductSpace Topology
open WeightedTorusHilbert WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open JointHolomorphicLaurentFourierCompatibility
namespace Ehrhart.ComplexSaturatedKillingFieldBridge
theorem _root_.solution (n : ℕ) :
    MeasurePreserving (realFundamentalEmbedding n)
      (unweightedFundamentalMeasure n)
      ((volume : Measure (Space n)).prod
        ((volume : Measure (Space n)).restrict
          {t : Space n |
            ∀ i : Fin n, t i ∈ Set.Ioc (0 : ℝ) ((0 : ℝ) + 1)})) := by
  let : IsFiniteMeasure (angularFundamentalMeasure n) := by
    rw [← (angularFundamentalEquiv_measurePreserving n).map_eq]
    infer_instance
  have hsub : MeasurePreserving
      (Subtype.val : angularFundamentalCell n → Space n)
      (angularFundamentalMeasure n)
      ((volume : Measure (Space n)).restrict
        {t : Space n |
          ∀ i : Fin n, t i ∈ Set.Ioc (0 : ℝ) ((0 : ℝ) + 1)}) := by
    exact measurePreserving_subtype_coe
      (angularFundamentalCell_set_measurable n)
  change MeasurePreserving
    (Prod.map id (Subtype.val : angularFundamentalCell n → Space n))
    ((volume : Measure (Space n)).prod
      (angularFundamentalMeasure n))
    ((volume : Measure (Space n)).prod
      ((volume : Measure (Space n)).restrict
        {t : Space n |
          ∀ i : Fin n, t i ∈ Set.Ioc (0 : ℝ) ((0 : ℝ) + 1)}))
  exact (MeasurePreserving.id
    (volume : Measure (Space n))).prod hsub
end Ehrhart.ComplexSaturatedKillingFieldBridge
