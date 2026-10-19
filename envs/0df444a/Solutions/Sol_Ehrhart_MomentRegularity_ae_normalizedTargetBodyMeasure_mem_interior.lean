-- Prove2me | solution 1 for Ehrhart.MomentRegularity.ae_normalizedTargetBodyMeasure_mem_interior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/d91afa23-cfa5-4288-8313-a91b979fa2fc

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MomentRegularity_normalizedTargetBodyMeasure_eq_interior_restrict

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
    {n : ℕ} (K : CenteredBody n) :
    ∀ᵐ p : Space n
      ∂(normalizedTargetBodyMeasure K),
      p ∈ interior K.carrier := by
  rw [normalizedTargetBodyMeasure_eq_interior_restrict K]
  exact Measure.ae_smul_measure
    (MeasureTheory.ae_restrict_mem
      isOpen_interior.measurableSet)
    (((volume : Measure (Space n)) K.carrier)⁻¹)
end Ehrhart.MomentRegularity
