-- Prove2me | solution 1 for Ehrhart.MomentRegularity.ae_finiteEnergySourceGradient_mem_interior_volume
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/b570a258-655c-42fa-8ee3-eea4f1edf074

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MomentRegularity_volume_absolutelyContinuous_finiteEnergySourceGibbs
import Theorems.Thm_Ehrhart_MomentRegularity_ae_finiteEnergySourceGradient_mem_interior_gibbs

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
      ∂(volume : Measure (Space n)),
      SpatialBergmanFatouScheffe.actualGradient
        F.potential x ∈ interior K.carrier := by
  exact
    (volume_absolutelyContinuous_finiteEnergySourceGibbs F).ae_le
      (ae_finiteEnergySourceGradient_mem_interior_gibbs F htransport)
end Ehrhart.MomentRegularity
