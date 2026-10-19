-- Prove2me | solution 1 for Ehrhart.MomentInteriorLegendre.locallyLipschitzOn_finiteEnergySourceLegendre_interior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/aa9ac326-5c49-404f-9823-969fd644ecd3

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MomentInteriorLegendre
open Set Function Filter MeasureTheory
open LaplaceAsymptotics MomentFunctionalCoercivity MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentMonotoneTransport
open scoped BigOperators ENNReal Topology
namespace Ehrhart.MomentInteriorLegendre
theorem _root_.solution
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport :
      finiteEnergySourceGradientPushforward F =
        normalizedTargetBodyMeasure K) :
    LocallyLipschitzOn (interior K.carrier)
      (legendreTransform F.potential) :=
  (convexOn_finiteEnergySourceLegendre_interior F htransport)
    |>.locallyLipschitzOn isOpen_interior
end Ehrhart.MomentInteriorLegendre
