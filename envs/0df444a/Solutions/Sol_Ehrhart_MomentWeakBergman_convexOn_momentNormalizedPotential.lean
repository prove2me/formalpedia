-- Prove2me | solution 1 for Ehrhart.MomentWeakBergman.convexOn_momentNormalizedPotential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/dd422b89-1ade-49a7-b1f6-20bf85d9a497

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
    (F : SourceFiniteEnergyPotential K) :
    ConvexOn ℝ Set.univ (momentNormalizedPotential F) := by
  have hpotential :
      (F.potential : Space n → ℝ) +
        (fun _ : Space n =>
          Real.log
            (finiteEnergySourcePartition F /
              normalizedVolume K.carrier)) =
        momentNormalizedPotential F := by
    funext x
    rfl
  rw [← hpotential]
  exact F.convex.add_const
    (Real.log
      (finiteEnergySourcePartition F /
        normalizedVolume K.carrier))
end Ehrhart.MomentWeakBergman
