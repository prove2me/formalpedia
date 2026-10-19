-- Prove2me | solution 1 for Ehrhart.MomentWeakBergman.momentNormalizedPotential_le_support_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/eff5c56b-cc85-44b1-bbd8-c806ba7ed98c

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MomentWeakBergman
open Set Function Filter MeasureTheory
open SupportFunction LaplaceAsymptotics MonomialIntegrability WeightedTorusHilbert MomentOptimizer
open MomentFirstVariation MomentTargetGeodesic MomentRegularity MomentInteriorLegendre
open MomentMoserTrudinger
open scoped BigOperators ENNReal InnerProductSpace Topology
namespace Ehrhart.MomentWeakBergman
theorem _root_.solution
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (x : Space n) :
    momentNormalizedPotential F x ≤
      supportFunction K.carrier x +
        Real.log
          (finiteEnergySourcePartition F /
            normalizedVolume K.carrier) := by
  unfold momentNormalizedPotential
  linarith [F.supportUpper x]
end Ehrhart.MomentWeakBergman
