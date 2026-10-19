-- Prove2me | solution 1 for Ehrhart.MomentRegularity.ae_finiteEnergySourceGradient_mem_interior_gibbs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/16ac4178-d238-4495-887f-5ca16480b3dd

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MomentRegularity_ae_normalizedTargetBodyMeasure_mem_interior

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MomentRegularity
open Set Function Filter MeasureTheory
open MomentOptimizer MomentWeakFirstVariation MomentFirstVariation MomentTargetGeodesic
open scoped ENNReal Topology
namespace Ehrhart.MomentRegularity
theorem _root_.solution
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport :
      finiteEnergySourceGradientPushforward F =
        normalizedTargetBodyMeasure K) :
    ∀ᵐ x : Space n
      ∂(finiteEnergySourceGibbsProbability F),
      SpatialBergmanFatouScheffe.actualGradient
        F.potential x ∈ interior K.carrier := by
  have htarget :
      ∀ᵐ p : Space n
        ∂(finiteEnergySourceGradientPushforward F),
        p ∈ interior K.carrier := by
    rw [htransport]
    exact ae_normalizedTargetBodyMeasure_mem_interior K
  unfold finiteEnergySourceGradientPushforward at htarget
  exact
    (MeasureTheory.ae_map_iff
      (measurable_finiteEnergySourceGradient F).aemeasurable
      isOpen_interior.measurableSet).mp htarget
end Ehrhart.MomentRegularity
