-- Prove2me | solution 1 for Ehrhart.MomentRegularity.normalizedTargetBodyMeasure_eq_interior_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/cdef9840-ea0a-4283-b9fd-21b15ed1ff7d

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
    normalizedTargetBodyMeasure K =
      ((volume : Measure (Space n)) K.carrier)⁻¹ •
        ((volume : Measure (Space n)).restrict
          (interior K.carrier)) := by
  have hrestrict :
      (volume : Measure (Space n)).restrict
          (interior K.carrier) =
        (volume : Measure (Space n)).restrict K.carrier :=
    Measure.restrict_congr_set
      (interior_ae_eq_of_null_frontier
        (K.convex.addHaar_frontier
          (volume : Measure (Space n))))
  unfold normalizedTargetBodyMeasure
  rw [hrestrict]
end Ehrhart.MomentRegularity
